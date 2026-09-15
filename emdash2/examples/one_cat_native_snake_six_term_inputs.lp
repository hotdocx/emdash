/* Whole native six-term inputs observations. */
require open emdash.emdash3_2_one_cat_native_snake_six_term_result;

// The first annotation retains the original native input.
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
  ⊢ (@one_cat_native_exact_arrow_pair_input K C (@additive_preadditive C Prod t Add) C1 t
  (@additive_terminal_object C Prod t Add) T0 P Q N (@kernel_adjunction_family_func K C (@additive_preadditive C
  Prod t Add) t (@additive_terminal_object C Prod t Add) P (@one_cat_native_snake_alpha_diagram K C
  (@additive_preadditive C Prod t Add) C1 t (@additive_terminal_object C Prod t Add) T0 P A B X D b c h))
  (@kernel_adjunction_family_func K C (@additive_preadditive C Prod t Add) t (@additive_terminal_object C Prod t
  Add) P (@transf_arrow_diagram_func K C B X b)) (@finite_arrow_tail_next (Functor_cat K C)
  (@OneCatNativeExactArrowPair K C (@additive_preadditive C Prod t Add) C1 t (@additive_terminal_object C Prod t
  Add) T0 P Q N) (succ (succ (succ zero))) (@kernel_adjunction_family_func K C (@additive_preadditive C Prod t
  Add) t (@additive_terminal_object C Prod t Add) P (@one_cat_native_snake_alpha_diagram K C
  (@additive_preadditive C Prod t Add) C1 t (@additive_terminal_object C Prod t Add) T0 P A B X D b c h))
  (@kernel_adjunction_family_func K C (@additive_preadditive C Prod t Add) t (@additive_terminal_object C Prod t
  Add) P (@transf_arrow_diagram_func K C B X b)) (@one_cat_native_snake_kernel_first K C (@additive_preadditive
  C Prod t Add) C1 t (@additive_terminal_object C Prod t Add) T0 P Q A B X D b c h)
  (@one_cat_native_snake_six_term_result K C C1 Prod t Add T0 P Q N A B X D b c h))
  (@one_cat_native_snake_kernel_first K C (@additive_preadditive C Prod t Add) C1 t (@additive_terminal_object C
  Prod t Add) T0 P Q A B X D b c h) (@finite_arrow_tail_arrow (Functor_cat K C) (@OneCatNativeExactArrowPair K C
  (@additive_preadditive C Prod t Add) C1 t (@additive_terminal_object C Prod t Add) T0 P Q N) (succ (succ (succ
  zero))) (@kernel_adjunction_family_func K C (@additive_preadditive C Prod t Add) t (@additive_terminal_object
  C Prod t Add) P (@one_cat_native_snake_alpha_diagram K C (@additive_preadditive C Prod t Add) C1 t
  (@additive_terminal_object C Prod t Add) T0 P A B X D b c h)) (@kernel_adjunction_family_func K C
  (@additive_preadditive C Prod t Add) t (@additive_terminal_object C Prod t Add) P (@transf_arrow_diagram_func
  K C B X b)) (@one_cat_native_snake_kernel_first K C (@additive_preadditive C Prod t Add) C1 t
  (@additive_terminal_object C Prod t Add) T0 P Q A B X D b c h) (@one_cat_native_snake_six_term_result K C C1
  Prod t Add T0 P Q N A B X D b c h)) (@finite_arrow_tail_step (Functor_cat K C) (@OneCatNativeExactArrowPair K
  C (@additive_preadditive C Prod t Add) C1 t (@additive_terminal_object C Prod t Add) T0 P Q N) (succ (succ
  (succ zero))) (@kernel_adjunction_family_func K C (@additive_preadditive C Prod t Add) t
  (@additive_terminal_object C Prod t Add) P (@one_cat_native_snake_alpha_diagram K C (@additive_preadditive C
  Prod t Add) C1 t (@additive_terminal_object C Prod t Add) T0 P A B X D b c h)) (@kernel_adjunction_family_func
  K C (@additive_preadditive C Prod t Add) t (@additive_terminal_object C Prod t Add) P
  (@transf_arrow_diagram_func K C B X b)) (@one_cat_native_snake_kernel_first K C (@additive_preadditive C Prod
  t Add) C1 t (@additive_terminal_object C Prod t Add) T0 P Q A B X D b c h)
  (@one_cat_native_snake_six_term_result K C C1 Prod t Add T0 P Q N A B X D b c h))) ≡
  (@one_cat_native_snake_first_exact_input K C C1 Prod t Add T0 P Q N A B X D b c h);

// The actual stored pair has its derived whole zero composite.
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
  ⊢ (@one_cat_native_exact_arrow_pair_zero K C (@additive_preadditive C Prod t Add) C1 t
  (@additive_terminal_object C Prod t Add) T0 P Q N (@kernel_adjunction_family_func K C (@additive_preadditive C
  Prod t Add) t (@additive_terminal_object C Prod t Add) P (@one_cat_native_snake_alpha_diagram K C
  (@additive_preadditive C Prod t Add) C1 t (@additive_terminal_object C Prod t Add) T0 P A B X D b c h))
  (@kernel_adjunction_family_func K C (@additive_preadditive C Prod t Add) t (@additive_terminal_object C Prod t
  Add) P (@transf_arrow_diagram_func K C B X b)) (@finite_arrow_tail_next (Functor_cat K C)
  (@OneCatNativeExactArrowPair K C (@additive_preadditive C Prod t Add) C1 t (@additive_terminal_object C Prod t
  Add) T0 P Q N) (succ (succ (succ zero))) (@kernel_adjunction_family_func K C (@additive_preadditive C Prod t
  Add) t (@additive_terminal_object C Prod t Add) P (@one_cat_native_snake_alpha_diagram K C
  (@additive_preadditive C Prod t Add) C1 t (@additive_terminal_object C Prod t Add) T0 P A B X D b c h))
  (@kernel_adjunction_family_func K C (@additive_preadditive C Prod t Add) t (@additive_terminal_object C Prod t
  Add) P (@transf_arrow_diagram_func K C B X b)) (@one_cat_native_snake_kernel_first K C (@additive_preadditive
  C Prod t Add) C1 t (@additive_terminal_object C Prod t Add) T0 P Q A B X D b c h)
  (@one_cat_native_snake_six_term_result K C C1 Prod t Add T0 P Q N A B X D b c h))
  (@one_cat_native_snake_kernel_first K C (@additive_preadditive C Prod t Add) C1 t (@additive_terminal_object C
  Prod t Add) T0 P Q A B X D b c h) (@finite_arrow_tail_arrow (Functor_cat K C) (@OneCatNativeExactArrowPair K C
  (@additive_preadditive C Prod t Add) C1 t (@additive_terminal_object C Prod t Add) T0 P Q N) (succ (succ (succ
  zero))) (@kernel_adjunction_family_func K C (@additive_preadditive C Prod t Add) t (@additive_terminal_object
  C Prod t Add) P (@one_cat_native_snake_alpha_diagram K C (@additive_preadditive C Prod t Add) C1 t
  (@additive_terminal_object C Prod t Add) T0 P A B X D b c h)) (@kernel_adjunction_family_func K C
  (@additive_preadditive C Prod t Add) t (@additive_terminal_object C Prod t Add) P (@transf_arrow_diagram_func
  K C B X b)) (@one_cat_native_snake_kernel_first K C (@additive_preadditive C Prod t Add) C1 t
  (@additive_terminal_object C Prod t Add) T0 P Q A B X D b c h) (@one_cat_native_snake_six_term_result K C C1
  Prod t Add T0 P Q N A B X D b c h)) (@finite_arrow_tail_step (Functor_cat K C) (@OneCatNativeExactArrowPair K
  C (@additive_preadditive C Prod t Add) C1 t (@additive_terminal_object C Prod t Add) T0 P Q N) (succ (succ
  (succ zero))) (@kernel_adjunction_family_func K C (@additive_preadditive C Prod t Add) t
  (@additive_terminal_object C Prod t Add) P (@one_cat_native_snake_alpha_diagram K C (@additive_preadditive C
  Prod t Add) C1 t (@additive_terminal_object C Prod t Add) T0 P A B X D b c h)) (@kernel_adjunction_family_func
  K C (@additive_preadditive C Prod t Add) t (@additive_terminal_object C Prod t Add) P
  (@transf_arrow_diagram_func K C B X b)) (@one_cat_native_snake_kernel_first K C (@additive_preadditive C Prod
  t Add) C1 t (@additive_terminal_object C Prod t Add) T0 P Q A B X D b c h)
  (@one_cat_native_snake_six_term_result K C C1 Prod t Add T0 P Q N A B X D b c h)))
  : τ (@= (@Transf K C (@kernel_adjunction_family_func K C (@additive_preadditive C Prod t Add) t
  (@additive_terminal_object C Prod t Add) P (@one_cat_native_snake_alpha_diagram K C (@additive_preadditive C
  Prod t Add) C1 t (@additive_terminal_object C Prod t Add) T0 P A B X D b c h)) (@finite_arrow_tail_next
  (Functor_cat K C) (@OneCatNativeExactArrowPair K C (@additive_preadditive C Prod t Add) C1 t
  (@additive_terminal_object C Prod t Add) T0 P Q N) (succ (succ (succ zero))) (@kernel_adjunction_family_func K
  C (@additive_preadditive C Prod t Add) t (@additive_terminal_object C Prod t Add) P
  (@one_cat_native_snake_alpha_diagram K C (@additive_preadditive C Prod t Add) C1 t (@additive_terminal_object
  C Prod t Add) T0 P A B X D b c h)) (@kernel_adjunction_family_func K C (@additive_preadditive C Prod t Add) t
  (@additive_terminal_object C Prod t Add) P (@transf_arrow_diagram_func K C B X b))
  (@one_cat_native_snake_kernel_first K C (@additive_preadditive C Prod t Add) C1 t (@additive_terminal_object C
  Prod t Add) T0 P Q A B X D b c h) (@one_cat_native_snake_six_term_result K C C1 Prod t Add T0 P Q N A B X D b
  c h))) (@comp_fapp0 (Functor_cat K C) (@kernel_adjunction_family_func K C (@additive_preadditive C Prod t Add)
  t (@additive_terminal_object C Prod t Add) P (@one_cat_native_snake_alpha_diagram K C (@additive_preadditive C
  Prod t Add) C1 t (@additive_terminal_object C Prod t Add) T0 P A B X D b c h)) (@kernel_adjunction_family_func
  K C (@additive_preadditive C Prod t Add) t (@additive_terminal_object C Prod t Add) P
  (@transf_arrow_diagram_func K C B X b)) (@finite_arrow_tail_next (Functor_cat K C)
  (@OneCatNativeExactArrowPair K C (@additive_preadditive C Prod t Add) C1 t (@additive_terminal_object C Prod t
  Add) T0 P Q N) (succ (succ (succ zero))) (@kernel_adjunction_family_func K C (@additive_preadditive C Prod t
  Add) t (@additive_terminal_object C Prod t Add) P (@one_cat_native_snake_alpha_diagram K C
  (@additive_preadditive C Prod t Add) C1 t (@additive_terminal_object C Prod t Add) T0 P A B X D b c h))
  (@kernel_adjunction_family_func K C (@additive_preadditive C Prod t Add) t (@additive_terminal_object C Prod t
  Add) P (@transf_arrow_diagram_func K C B X b)) (@one_cat_native_snake_kernel_first K C (@additive_preadditive
  C Prod t Add) C1 t (@additive_terminal_object C Prod t Add) T0 P Q A B X D b c h)
  (@one_cat_native_snake_six_term_result K C C1 Prod t Add T0 P Q N A B X D b c h)) (@finite_arrow_tail_arrow
  (Functor_cat K C) (@OneCatNativeExactArrowPair K C (@additive_preadditive C Prod t Add) C1 t
  (@additive_terminal_object C Prod t Add) T0 P Q N) (succ (succ (succ zero))) (@kernel_adjunction_family_func K
  C (@additive_preadditive C Prod t Add) t (@additive_terminal_object C Prod t Add) P
  (@one_cat_native_snake_alpha_diagram K C (@additive_preadditive C Prod t Add) C1 t (@additive_terminal_object
  C Prod t Add) T0 P A B X D b c h)) (@kernel_adjunction_family_func K C (@additive_preadditive C Prod t Add) t
  (@additive_terminal_object C Prod t Add) P (@transf_arrow_diagram_func K C B X b))
  (@one_cat_native_snake_kernel_first K C (@additive_preadditive C Prod t Add) C1 t (@additive_terminal_object C
  Prod t Add) T0 P Q A B X D b c h) (@one_cat_native_snake_six_term_result K C C1 Prod t Add T0 P Q N A B X D b
  c h)) (@one_cat_native_snake_kernel_first K C (@additive_preadditive C Prod t Add) C1 t
  (@additive_terminal_object C Prod t Add) T0 P Q A B X D b c h)) (@zero_arrow_family_zero_transf K C t
  (@additive_terminal_object C Prod t Add) T0 (@kernel_adjunction_family_func K C (@additive_preadditive C Prod
  t Add) t (@additive_terminal_object C Prod t Add) P (@one_cat_native_snake_alpha_diagram K C
  (@additive_preadditive C Prod t Add) C1 t (@additive_terminal_object C Prod t Add) T0 P A B X D b c h))
  (@finite_arrow_tail_next (Functor_cat K C) (@OneCatNativeExactArrowPair K C (@additive_preadditive C Prod t
  Add) C1 t (@additive_terminal_object C Prod t Add) T0 P Q N) (succ (succ (succ zero)))
  (@kernel_adjunction_family_func K C (@additive_preadditive C Prod t Add) t (@additive_terminal_object C Prod t
  Add) P (@one_cat_native_snake_alpha_diagram K C (@additive_preadditive C Prod t Add) C1 t
  (@additive_terminal_object C Prod t Add) T0 P A B X D b c h)) (@kernel_adjunction_family_func K C
  (@additive_preadditive C Prod t Add) t (@additive_terminal_object C Prod t Add) P (@transf_arrow_diagram_func
  K C B X b)) (@one_cat_native_snake_kernel_first K C (@additive_preadditive C Prod t Add) C1 t
  (@additive_terminal_object C Prod t Add) T0 P Q A B X D b c h) (@one_cat_native_snake_six_term_result K C C1
  Prod t Add T0 P Q N A B X D b c h))));

// The second annotation retains the original native input.
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
  ⊢ (@one_cat_native_exact_arrow_pair_input K C (@additive_preadditive C Prod t Add) C1 t
  (@additive_terminal_object C Prod t Add) T0 P Q N (@kernel_adjunction_family_func K C (@additive_preadditive C
  Prod t Add) t (@additive_terminal_object C Prod t Add) P (@transf_arrow_diagram_func K C B X b))
  (@finite_arrow_tail_next (Functor_cat K C) (@OneCatNativeExactArrowPair K C (@additive_preadditive C Prod t
  Add) C1 t (@additive_terminal_object C Prod t Add) T0 P Q N) (succ (succ (succ zero)))
  (@kernel_adjunction_family_func K C (@additive_preadditive C Prod t Add) t (@additive_terminal_object C Prod t
  Add) P (@one_cat_native_snake_alpha_diagram K C (@additive_preadditive C Prod t Add) C1 t
  (@additive_terminal_object C Prod t Add) T0 P A B X D b c h)) (@kernel_adjunction_family_func K C
  (@additive_preadditive C Prod t Add) t (@additive_terminal_object C Prod t Add) P (@transf_arrow_diagram_func
  K C B X b)) (@one_cat_native_snake_kernel_first K C (@additive_preadditive C Prod t Add) C1 t
  (@additive_terminal_object C Prod t Add) T0 P Q A B X D b c h) (@one_cat_native_snake_six_term_result K C C1
  Prod t Add T0 P Q N A B X D b c h)) (@finite_arrow_tail_next (Functor_cat K C) (@OneCatNativeExactArrowPair K
  C (@additive_preadditive C Prod t Add) C1 t (@additive_terminal_object C Prod t Add) T0 P Q N) (succ (succ
  zero)) (@kernel_adjunction_family_func K C (@additive_preadditive C Prod t Add) t (@additive_terminal_object C
  Prod t Add) P (@transf_arrow_diagram_func K C B X b)) (@finite_arrow_tail_next (Functor_cat K C)
  (@OneCatNativeExactArrowPair K C (@additive_preadditive C Prod t Add) C1 t (@additive_terminal_object C Prod t
  Add) T0 P Q N) (succ (succ (succ zero))) (@kernel_adjunction_family_func K C (@additive_preadditive C Prod t
  Add) t (@additive_terminal_object C Prod t Add) P (@one_cat_native_snake_alpha_diagram K C
  (@additive_preadditive C Prod t Add) C1 t (@additive_terminal_object C Prod t Add) T0 P A B X D b c h))
  (@kernel_adjunction_family_func K C (@additive_preadditive C Prod t Add) t (@additive_terminal_object C Prod t
  Add) P (@transf_arrow_diagram_func K C B X b)) (@one_cat_native_snake_kernel_first K C (@additive_preadditive
  C Prod t Add) C1 t (@additive_terminal_object C Prod t Add) T0 P Q A B X D b c h)
  (@one_cat_native_snake_six_term_result K C C1 Prod t Add T0 P Q N A B X D b c h)) (@finite_arrow_tail_arrow
  (Functor_cat K C) (@OneCatNativeExactArrowPair K C (@additive_preadditive C Prod t Add) C1 t
  (@additive_terminal_object C Prod t Add) T0 P Q N) (succ (succ (succ zero))) (@kernel_adjunction_family_func K
  C (@additive_preadditive C Prod t Add) t (@additive_terminal_object C Prod t Add) P
  (@one_cat_native_snake_alpha_diagram K C (@additive_preadditive C Prod t Add) C1 t (@additive_terminal_object
  C Prod t Add) T0 P A B X D b c h)) (@kernel_adjunction_family_func K C (@additive_preadditive C Prod t Add) t
  (@additive_terminal_object C Prod t Add) P (@transf_arrow_diagram_func K C B X b))
  (@one_cat_native_snake_kernel_first K C (@additive_preadditive C Prod t Add) C1 t (@additive_terminal_object C
  Prod t Add) T0 P Q A B X D b c h) (@one_cat_native_snake_six_term_result K C C1 Prod t Add T0 P Q N A B X D b
  c h)) (@finite_arrow_tail_rest (Functor_cat K C) (@OneCatNativeExactArrowPair K C (@additive_preadditive C
  Prod t Add) C1 t (@additive_terminal_object C Prod t Add) T0 P Q N) (succ (succ (succ zero)))
  (@kernel_adjunction_family_func K C (@additive_preadditive C Prod t Add) t (@additive_terminal_object C Prod t
  Add) P (@one_cat_native_snake_alpha_diagram K C (@additive_preadditive C Prod t Add) C1 t
  (@additive_terminal_object C Prod t Add) T0 P A B X D b c h)) (@kernel_adjunction_family_func K C
  (@additive_preadditive C Prod t Add) t (@additive_terminal_object C Prod t Add) P (@transf_arrow_diagram_func
  K C B X b)) (@one_cat_native_snake_kernel_first K C (@additive_preadditive C Prod t Add) C1 t
  (@additive_terminal_object C Prod t Add) T0 P Q A B X D b c h) (@one_cat_native_snake_six_term_result K C C1
  Prod t Add T0 P Q N A B X D b c h))) (@finite_arrow_tail_arrow (Functor_cat K C) (@OneCatNativeExactArrowPair
  K C (@additive_preadditive C Prod t Add) C1 t (@additive_terminal_object C Prod t Add) T0 P Q N) (succ (succ
  (succ zero))) (@kernel_adjunction_family_func K C (@additive_preadditive C Prod t Add) t
  (@additive_terminal_object C Prod t Add) P (@one_cat_native_snake_alpha_diagram K C (@additive_preadditive C
  Prod t Add) C1 t (@additive_terminal_object C Prod t Add) T0 P A B X D b c h)) (@kernel_adjunction_family_func
  K C (@additive_preadditive C Prod t Add) t (@additive_terminal_object C Prod t Add) P
  (@transf_arrow_diagram_func K C B X b)) (@one_cat_native_snake_kernel_first K C (@additive_preadditive C Prod
  t Add) C1 t (@additive_terminal_object C Prod t Add) T0 P Q A B X D b c h)
  (@one_cat_native_snake_six_term_result K C C1 Prod t Add T0 P Q N A B X D b c h)) (@finite_arrow_tail_arrow
  (Functor_cat K C) (@OneCatNativeExactArrowPair K C (@additive_preadditive C Prod t Add) C1 t
  (@additive_terminal_object C Prod t Add) T0 P Q N) (succ (succ zero)) (@kernel_adjunction_family_func K C
  (@additive_preadditive C Prod t Add) t (@additive_terminal_object C Prod t Add) P (@transf_arrow_diagram_func
  K C B X b)) (@finite_arrow_tail_next (Functor_cat K C) (@OneCatNativeExactArrowPair K C (@additive_preadditive
  C Prod t Add) C1 t (@additive_terminal_object C Prod t Add) T0 P Q N) (succ (succ (succ zero)))
  (@kernel_adjunction_family_func K C (@additive_preadditive C Prod t Add) t (@additive_terminal_object C Prod t
  Add) P (@one_cat_native_snake_alpha_diagram K C (@additive_preadditive C Prod t Add) C1 t
  (@additive_terminal_object C Prod t Add) T0 P A B X D b c h)) (@kernel_adjunction_family_func K C
  (@additive_preadditive C Prod t Add) t (@additive_terminal_object C Prod t Add) P (@transf_arrow_diagram_func
  K C B X b)) (@one_cat_native_snake_kernel_first K C (@additive_preadditive C Prod t Add) C1 t
  (@additive_terminal_object C Prod t Add) T0 P Q A B X D b c h) (@one_cat_native_snake_six_term_result K C C1
  Prod t Add T0 P Q N A B X D b c h)) (@finite_arrow_tail_arrow (Functor_cat K C) (@OneCatNativeExactArrowPair K
  C (@additive_preadditive C Prod t Add) C1 t (@additive_terminal_object C Prod t Add) T0 P Q N) (succ (succ
  (succ zero))) (@kernel_adjunction_family_func K C (@additive_preadditive C Prod t Add) t
  (@additive_terminal_object C Prod t Add) P (@one_cat_native_snake_alpha_diagram K C (@additive_preadditive C
  Prod t Add) C1 t (@additive_terminal_object C Prod t Add) T0 P A B X D b c h)) (@kernel_adjunction_family_func
  K C (@additive_preadditive C Prod t Add) t (@additive_terminal_object C Prod t Add) P
  (@transf_arrow_diagram_func K C B X b)) (@one_cat_native_snake_kernel_first K C (@additive_preadditive C Prod
  t Add) C1 t (@additive_terminal_object C Prod t Add) T0 P Q A B X D b c h)
  (@one_cat_native_snake_six_term_result K C C1 Prod t Add T0 P Q N A B X D b c h)) (@finite_arrow_tail_rest
  (Functor_cat K C) (@OneCatNativeExactArrowPair K C (@additive_preadditive C Prod t Add) C1 t
  (@additive_terminal_object C Prod t Add) T0 P Q N) (succ (succ (succ zero))) (@kernel_adjunction_family_func K
  C (@additive_preadditive C Prod t Add) t (@additive_terminal_object C Prod t Add) P
  (@one_cat_native_snake_alpha_diagram K C (@additive_preadditive C Prod t Add) C1 t (@additive_terminal_object
  C Prod t Add) T0 P A B X D b c h)) (@kernel_adjunction_family_func K C (@additive_preadditive C Prod t Add) t
  (@additive_terminal_object C Prod t Add) P (@transf_arrow_diagram_func K C B X b))
  (@one_cat_native_snake_kernel_first K C (@additive_preadditive C Prod t Add) C1 t (@additive_terminal_object C
  Prod t Add) T0 P Q A B X D b c h) (@one_cat_native_snake_six_term_result K C C1 Prod t Add T0 P Q N A B X D b
  c h))) (@finite_arrow_tail_step (Functor_cat K C) (@OneCatNativeExactArrowPair K C (@additive_preadditive C
  Prod t Add) C1 t (@additive_terminal_object C Prod t Add) T0 P Q N) (succ (succ zero))
  (@kernel_adjunction_family_func K C (@additive_preadditive C Prod t Add) t (@additive_terminal_object C Prod t
  Add) P (@transf_arrow_diagram_func K C B X b)) (@finite_arrow_tail_next (Functor_cat K C)
  (@OneCatNativeExactArrowPair K C (@additive_preadditive C Prod t Add) C1 t (@additive_terminal_object C Prod t
  Add) T0 P Q N) (succ (succ (succ zero))) (@kernel_adjunction_family_func K C (@additive_preadditive C Prod t
  Add) t (@additive_terminal_object C Prod t Add) P (@one_cat_native_snake_alpha_diagram K C
  (@additive_preadditive C Prod t Add) C1 t (@additive_terminal_object C Prod t Add) T0 P A B X D b c h))
  (@kernel_adjunction_family_func K C (@additive_preadditive C Prod t Add) t (@additive_terminal_object C Prod t
  Add) P (@transf_arrow_diagram_func K C B X b)) (@one_cat_native_snake_kernel_first K C (@additive_preadditive
  C Prod t Add) C1 t (@additive_terminal_object C Prod t Add) T0 P Q A B X D b c h)
  (@one_cat_native_snake_six_term_result K C C1 Prod t Add T0 P Q N A B X D b c h)) (@finite_arrow_tail_arrow
  (Functor_cat K C) (@OneCatNativeExactArrowPair K C (@additive_preadditive C Prod t Add) C1 t
  (@additive_terminal_object C Prod t Add) T0 P Q N) (succ (succ (succ zero))) (@kernel_adjunction_family_func K
  C (@additive_preadditive C Prod t Add) t (@additive_terminal_object C Prod t Add) P
  (@one_cat_native_snake_alpha_diagram K C (@additive_preadditive C Prod t Add) C1 t (@additive_terminal_object
  C Prod t Add) T0 P A B X D b c h)) (@kernel_adjunction_family_func K C (@additive_preadditive C Prod t Add) t
  (@additive_terminal_object C Prod t Add) P (@transf_arrow_diagram_func K C B X b))
  (@one_cat_native_snake_kernel_first K C (@additive_preadditive C Prod t Add) C1 t (@additive_terminal_object C
  Prod t Add) T0 P Q A B X D b c h) (@one_cat_native_snake_six_term_result K C C1 Prod t Add T0 P Q N A B X D b
  c h)) (@finite_arrow_tail_rest (Functor_cat K C) (@OneCatNativeExactArrowPair K C (@additive_preadditive C
  Prod t Add) C1 t (@additive_terminal_object C Prod t Add) T0 P Q N) (succ (succ (succ zero)))
  (@kernel_adjunction_family_func K C (@additive_preadditive C Prod t Add) t (@additive_terminal_object C Prod t
  Add) P (@one_cat_native_snake_alpha_diagram K C (@additive_preadditive C Prod t Add) C1 t
  (@additive_terminal_object C Prod t Add) T0 P A B X D b c h)) (@kernel_adjunction_family_func K C
  (@additive_preadditive C Prod t Add) t (@additive_terminal_object C Prod t Add) P (@transf_arrow_diagram_func
  K C B X b)) (@one_cat_native_snake_kernel_first K C (@additive_preadditive C Prod t Add) C1 t
  (@additive_terminal_object C Prod t Add) T0 P Q A B X D b c h) (@one_cat_native_snake_six_term_result K C C1
  Prod t Add T0 P Q N A B X D b c h)))) ≡ (@one_cat_native_snake_second_exact_input K C C1 Prod t Add T0 P Q N A
  B X D b c h);

// The actual stored pair has its derived whole zero composite.
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
  ⊢ (@one_cat_native_exact_arrow_pair_zero K C (@additive_preadditive C Prod t Add) C1 t
  (@additive_terminal_object C Prod t Add) T0 P Q N (@kernel_adjunction_family_func K C (@additive_preadditive C
  Prod t Add) t (@additive_terminal_object C Prod t Add) P (@transf_arrow_diagram_func K C B X b))
  (@finite_arrow_tail_next (Functor_cat K C) (@OneCatNativeExactArrowPair K C (@additive_preadditive C Prod t
  Add) C1 t (@additive_terminal_object C Prod t Add) T0 P Q N) (succ (succ (succ zero)))
  (@kernel_adjunction_family_func K C (@additive_preadditive C Prod t Add) t (@additive_terminal_object C Prod t
  Add) P (@one_cat_native_snake_alpha_diagram K C (@additive_preadditive C Prod t Add) C1 t
  (@additive_terminal_object C Prod t Add) T0 P A B X D b c h)) (@kernel_adjunction_family_func K C
  (@additive_preadditive C Prod t Add) t (@additive_terminal_object C Prod t Add) P (@transf_arrow_diagram_func
  K C B X b)) (@one_cat_native_snake_kernel_first K C (@additive_preadditive C Prod t Add) C1 t
  (@additive_terminal_object C Prod t Add) T0 P Q A B X D b c h) (@one_cat_native_snake_six_term_result K C C1
  Prod t Add T0 P Q N A B X D b c h)) (@finite_arrow_tail_next (Functor_cat K C) (@OneCatNativeExactArrowPair K
  C (@additive_preadditive C Prod t Add) C1 t (@additive_terminal_object C Prod t Add) T0 P Q N) (succ (succ
  zero)) (@kernel_adjunction_family_func K C (@additive_preadditive C Prod t Add) t (@additive_terminal_object C
  Prod t Add) P (@transf_arrow_diagram_func K C B X b)) (@finite_arrow_tail_next (Functor_cat K C)
  (@OneCatNativeExactArrowPair K C (@additive_preadditive C Prod t Add) C1 t (@additive_terminal_object C Prod t
  Add) T0 P Q N) (succ (succ (succ zero))) (@kernel_adjunction_family_func K C (@additive_preadditive C Prod t
  Add) t (@additive_terminal_object C Prod t Add) P (@one_cat_native_snake_alpha_diagram K C
  (@additive_preadditive C Prod t Add) C1 t (@additive_terminal_object C Prod t Add) T0 P A B X D b c h))
  (@kernel_adjunction_family_func K C (@additive_preadditive C Prod t Add) t (@additive_terminal_object C Prod t
  Add) P (@transf_arrow_diagram_func K C B X b)) (@one_cat_native_snake_kernel_first K C (@additive_preadditive
  C Prod t Add) C1 t (@additive_terminal_object C Prod t Add) T0 P Q A B X D b c h)
  (@one_cat_native_snake_six_term_result K C C1 Prod t Add T0 P Q N A B X D b c h)) (@finite_arrow_tail_arrow
  (Functor_cat K C) (@OneCatNativeExactArrowPair K C (@additive_preadditive C Prod t Add) C1 t
  (@additive_terminal_object C Prod t Add) T0 P Q N) (succ (succ (succ zero))) (@kernel_adjunction_family_func K
  C (@additive_preadditive C Prod t Add) t (@additive_terminal_object C Prod t Add) P
  (@one_cat_native_snake_alpha_diagram K C (@additive_preadditive C Prod t Add) C1 t (@additive_terminal_object
  C Prod t Add) T0 P A B X D b c h)) (@kernel_adjunction_family_func K C (@additive_preadditive C Prod t Add) t
  (@additive_terminal_object C Prod t Add) P (@transf_arrow_diagram_func K C B X b))
  (@one_cat_native_snake_kernel_first K C (@additive_preadditive C Prod t Add) C1 t (@additive_terminal_object C
  Prod t Add) T0 P Q A B X D b c h) (@one_cat_native_snake_six_term_result K C C1 Prod t Add T0 P Q N A B X D b
  c h)) (@finite_arrow_tail_rest (Functor_cat K C) (@OneCatNativeExactArrowPair K C (@additive_preadditive C
  Prod t Add) C1 t (@additive_terminal_object C Prod t Add) T0 P Q N) (succ (succ (succ zero)))
  (@kernel_adjunction_family_func K C (@additive_preadditive C Prod t Add) t (@additive_terminal_object C Prod t
  Add) P (@one_cat_native_snake_alpha_diagram K C (@additive_preadditive C Prod t Add) C1 t
  (@additive_terminal_object C Prod t Add) T0 P A B X D b c h)) (@kernel_adjunction_family_func K C
  (@additive_preadditive C Prod t Add) t (@additive_terminal_object C Prod t Add) P (@transf_arrow_diagram_func
  K C B X b)) (@one_cat_native_snake_kernel_first K C (@additive_preadditive C Prod t Add) C1 t
  (@additive_terminal_object C Prod t Add) T0 P Q A B X D b c h) (@one_cat_native_snake_six_term_result K C C1
  Prod t Add T0 P Q N A B X D b c h))) (@finite_arrow_tail_arrow (Functor_cat K C) (@OneCatNativeExactArrowPair
  K C (@additive_preadditive C Prod t Add) C1 t (@additive_terminal_object C Prod t Add) T0 P Q N) (succ (succ
  (succ zero))) (@kernel_adjunction_family_func K C (@additive_preadditive C Prod t Add) t
  (@additive_terminal_object C Prod t Add) P (@one_cat_native_snake_alpha_diagram K C (@additive_preadditive C
  Prod t Add) C1 t (@additive_terminal_object C Prod t Add) T0 P A B X D b c h)) (@kernel_adjunction_family_func
  K C (@additive_preadditive C Prod t Add) t (@additive_terminal_object C Prod t Add) P
  (@transf_arrow_diagram_func K C B X b)) (@one_cat_native_snake_kernel_first K C (@additive_preadditive C Prod
  t Add) C1 t (@additive_terminal_object C Prod t Add) T0 P Q A B X D b c h)
  (@one_cat_native_snake_six_term_result K C C1 Prod t Add T0 P Q N A B X D b c h)) (@finite_arrow_tail_arrow
  (Functor_cat K C) (@OneCatNativeExactArrowPair K C (@additive_preadditive C Prod t Add) C1 t
  (@additive_terminal_object C Prod t Add) T0 P Q N) (succ (succ zero)) (@kernel_adjunction_family_func K C
  (@additive_preadditive C Prod t Add) t (@additive_terminal_object C Prod t Add) P (@transf_arrow_diagram_func
  K C B X b)) (@finite_arrow_tail_next (Functor_cat K C) (@OneCatNativeExactArrowPair K C (@additive_preadditive
  C Prod t Add) C1 t (@additive_terminal_object C Prod t Add) T0 P Q N) (succ (succ (succ zero)))
  (@kernel_adjunction_family_func K C (@additive_preadditive C Prod t Add) t (@additive_terminal_object C Prod t
  Add) P (@one_cat_native_snake_alpha_diagram K C (@additive_preadditive C Prod t Add) C1 t
  (@additive_terminal_object C Prod t Add) T0 P A B X D b c h)) (@kernel_adjunction_family_func K C
  (@additive_preadditive C Prod t Add) t (@additive_terminal_object C Prod t Add) P (@transf_arrow_diagram_func
  K C B X b)) (@one_cat_native_snake_kernel_first K C (@additive_preadditive C Prod t Add) C1 t
  (@additive_terminal_object C Prod t Add) T0 P Q A B X D b c h) (@one_cat_native_snake_six_term_result K C C1
  Prod t Add T0 P Q N A B X D b c h)) (@finite_arrow_tail_arrow (Functor_cat K C) (@OneCatNativeExactArrowPair K
  C (@additive_preadditive C Prod t Add) C1 t (@additive_terminal_object C Prod t Add) T0 P Q N) (succ (succ
  (succ zero))) (@kernel_adjunction_family_func K C (@additive_preadditive C Prod t Add) t
  (@additive_terminal_object C Prod t Add) P (@one_cat_native_snake_alpha_diagram K C (@additive_preadditive C
  Prod t Add) C1 t (@additive_terminal_object C Prod t Add) T0 P A B X D b c h)) (@kernel_adjunction_family_func
  K C (@additive_preadditive C Prod t Add) t (@additive_terminal_object C Prod t Add) P
  (@transf_arrow_diagram_func K C B X b)) (@one_cat_native_snake_kernel_first K C (@additive_preadditive C Prod
  t Add) C1 t (@additive_terminal_object C Prod t Add) T0 P Q A B X D b c h)
  (@one_cat_native_snake_six_term_result K C C1 Prod t Add T0 P Q N A B X D b c h)) (@finite_arrow_tail_rest
  (Functor_cat K C) (@OneCatNativeExactArrowPair K C (@additive_preadditive C Prod t Add) C1 t
  (@additive_terminal_object C Prod t Add) T0 P Q N) (succ (succ (succ zero))) (@kernel_adjunction_family_func K
  C (@additive_preadditive C Prod t Add) t (@additive_terminal_object C Prod t Add) P
  (@one_cat_native_snake_alpha_diagram K C (@additive_preadditive C Prod t Add) C1 t (@additive_terminal_object
  C Prod t Add) T0 P A B X D b c h)) (@kernel_adjunction_family_func K C (@additive_preadditive C Prod t Add) t
  (@additive_terminal_object C Prod t Add) P (@transf_arrow_diagram_func K C B X b))
  (@one_cat_native_snake_kernel_first K C (@additive_preadditive C Prod t Add) C1 t (@additive_terminal_object C
  Prod t Add) T0 P Q A B X D b c h) (@one_cat_native_snake_six_term_result K C C1 Prod t Add T0 P Q N A B X D b
  c h))) (@finite_arrow_tail_step (Functor_cat K C) (@OneCatNativeExactArrowPair K C (@additive_preadditive C
  Prod t Add) C1 t (@additive_terminal_object C Prod t Add) T0 P Q N) (succ (succ zero))
  (@kernel_adjunction_family_func K C (@additive_preadditive C Prod t Add) t (@additive_terminal_object C Prod t
  Add) P (@transf_arrow_diagram_func K C B X b)) (@finite_arrow_tail_next (Functor_cat K C)
  (@OneCatNativeExactArrowPair K C (@additive_preadditive C Prod t Add) C1 t (@additive_terminal_object C Prod t
  Add) T0 P Q N) (succ (succ (succ zero))) (@kernel_adjunction_family_func K C (@additive_preadditive C Prod t
  Add) t (@additive_terminal_object C Prod t Add) P (@one_cat_native_snake_alpha_diagram K C
  (@additive_preadditive C Prod t Add) C1 t (@additive_terminal_object C Prod t Add) T0 P A B X D b c h))
  (@kernel_adjunction_family_func K C (@additive_preadditive C Prod t Add) t (@additive_terminal_object C Prod t
  Add) P (@transf_arrow_diagram_func K C B X b)) (@one_cat_native_snake_kernel_first K C (@additive_preadditive
  C Prod t Add) C1 t (@additive_terminal_object C Prod t Add) T0 P Q A B X D b c h)
  (@one_cat_native_snake_six_term_result K C C1 Prod t Add T0 P Q N A B X D b c h)) (@finite_arrow_tail_arrow
  (Functor_cat K C) (@OneCatNativeExactArrowPair K C (@additive_preadditive C Prod t Add) C1 t
  (@additive_terminal_object C Prod t Add) T0 P Q N) (succ (succ (succ zero))) (@kernel_adjunction_family_func K
  C (@additive_preadditive C Prod t Add) t (@additive_terminal_object C Prod t Add) P
  (@one_cat_native_snake_alpha_diagram K C (@additive_preadditive C Prod t Add) C1 t (@additive_terminal_object
  C Prod t Add) T0 P A B X D b c h)) (@kernel_adjunction_family_func K C (@additive_preadditive C Prod t Add) t
  (@additive_terminal_object C Prod t Add) P (@transf_arrow_diagram_func K C B X b))
  (@one_cat_native_snake_kernel_first K C (@additive_preadditive C Prod t Add) C1 t (@additive_terminal_object C
  Prod t Add) T0 P Q A B X D b c h) (@one_cat_native_snake_six_term_result K C C1 Prod t Add T0 P Q N A B X D b
  c h)) (@finite_arrow_tail_rest (Functor_cat K C) (@OneCatNativeExactArrowPair K C (@additive_preadditive C
  Prod t Add) C1 t (@additive_terminal_object C Prod t Add) T0 P Q N) (succ (succ (succ zero)))
  (@kernel_adjunction_family_func K C (@additive_preadditive C Prod t Add) t (@additive_terminal_object C Prod t
  Add) P (@one_cat_native_snake_alpha_diagram K C (@additive_preadditive C Prod t Add) C1 t
  (@additive_terminal_object C Prod t Add) T0 P A B X D b c h)) (@kernel_adjunction_family_func K C
  (@additive_preadditive C Prod t Add) t (@additive_terminal_object C Prod t Add) P (@transf_arrow_diagram_func
  K C B X b)) (@one_cat_native_snake_kernel_first K C (@additive_preadditive C Prod t Add) C1 t
  (@additive_terminal_object C Prod t Add) T0 P Q A B X D b c h) (@one_cat_native_snake_six_term_result K C C1
  Prod t Add T0 P Q N A B X D b c h))))
  : τ (@= (@Transf K C (@kernel_adjunction_family_func K C (@additive_preadditive C Prod t Add) t
  (@additive_terminal_object C Prod t Add) P (@transf_arrow_diagram_func K C B X b)) (@finite_arrow_tail_next
  (Functor_cat K C) (@OneCatNativeExactArrowPair K C (@additive_preadditive C Prod t Add) C1 t
  (@additive_terminal_object C Prod t Add) T0 P Q N) (succ (succ zero)) (@kernel_adjunction_family_func K C
  (@additive_preadditive C Prod t Add) t (@additive_terminal_object C Prod t Add) P (@transf_arrow_diagram_func
  K C B X b)) (@finite_arrow_tail_next (Functor_cat K C) (@OneCatNativeExactArrowPair K C (@additive_preadditive
  C Prod t Add) C1 t (@additive_terminal_object C Prod t Add) T0 P Q N) (succ (succ (succ zero)))
  (@kernel_adjunction_family_func K C (@additive_preadditive C Prod t Add) t (@additive_terminal_object C Prod t
  Add) P (@one_cat_native_snake_alpha_diagram K C (@additive_preadditive C Prod t Add) C1 t
  (@additive_terminal_object C Prod t Add) T0 P A B X D b c h)) (@kernel_adjunction_family_func K C
  (@additive_preadditive C Prod t Add) t (@additive_terminal_object C Prod t Add) P (@transf_arrow_diagram_func
  K C B X b)) (@one_cat_native_snake_kernel_first K C (@additive_preadditive C Prod t Add) C1 t
  (@additive_terminal_object C Prod t Add) T0 P Q A B X D b c h) (@one_cat_native_snake_six_term_result K C C1
  Prod t Add T0 P Q N A B X D b c h)) (@finite_arrow_tail_arrow (Functor_cat K C) (@OneCatNativeExactArrowPair K
  C (@additive_preadditive C Prod t Add) C1 t (@additive_terminal_object C Prod t Add) T0 P Q N) (succ (succ
  (succ zero))) (@kernel_adjunction_family_func K C (@additive_preadditive C Prod t Add) t
  (@additive_terminal_object C Prod t Add) P (@one_cat_native_snake_alpha_diagram K C (@additive_preadditive C
  Prod t Add) C1 t (@additive_terminal_object C Prod t Add) T0 P A B X D b c h)) (@kernel_adjunction_family_func
  K C (@additive_preadditive C Prod t Add) t (@additive_terminal_object C Prod t Add) P
  (@transf_arrow_diagram_func K C B X b)) (@one_cat_native_snake_kernel_first K C (@additive_preadditive C Prod
  t Add) C1 t (@additive_terminal_object C Prod t Add) T0 P Q A B X D b c h)
  (@one_cat_native_snake_six_term_result K C C1 Prod t Add T0 P Q N A B X D b c h)) (@finite_arrow_tail_rest
  (Functor_cat K C) (@OneCatNativeExactArrowPair K C (@additive_preadditive C Prod t Add) C1 t
  (@additive_terminal_object C Prod t Add) T0 P Q N) (succ (succ (succ zero))) (@kernel_adjunction_family_func K
  C (@additive_preadditive C Prod t Add) t (@additive_terminal_object C Prod t Add) P
  (@one_cat_native_snake_alpha_diagram K C (@additive_preadditive C Prod t Add) C1 t (@additive_terminal_object
  C Prod t Add) T0 P A B X D b c h)) (@kernel_adjunction_family_func K C (@additive_preadditive C Prod t Add) t
  (@additive_terminal_object C Prod t Add) P (@transf_arrow_diagram_func K C B X b))
  (@one_cat_native_snake_kernel_first K C (@additive_preadditive C Prod t Add) C1 t (@additive_terminal_object C
  Prod t Add) T0 P Q A B X D b c h) (@one_cat_native_snake_six_term_result K C C1 Prod t Add T0 P Q N A B X D b
  c h)))) (@comp_fapp0 (Functor_cat K C) (@kernel_adjunction_family_func K C (@additive_preadditive C Prod t
  Add) t (@additive_terminal_object C Prod t Add) P (@transf_arrow_diagram_func K C B X b))
  (@finite_arrow_tail_next (Functor_cat K C) (@OneCatNativeExactArrowPair K C (@additive_preadditive C Prod t
  Add) C1 t (@additive_terminal_object C Prod t Add) T0 P Q N) (succ (succ (succ zero)))
  (@kernel_adjunction_family_func K C (@additive_preadditive C Prod t Add) t (@additive_terminal_object C Prod t
  Add) P (@one_cat_native_snake_alpha_diagram K C (@additive_preadditive C Prod t Add) C1 t
  (@additive_terminal_object C Prod t Add) T0 P A B X D b c h)) (@kernel_adjunction_family_func K C
  (@additive_preadditive C Prod t Add) t (@additive_terminal_object C Prod t Add) P (@transf_arrow_diagram_func
  K C B X b)) (@one_cat_native_snake_kernel_first K C (@additive_preadditive C Prod t Add) C1 t
  (@additive_terminal_object C Prod t Add) T0 P Q A B X D b c h) (@one_cat_native_snake_six_term_result K C C1
  Prod t Add T0 P Q N A B X D b c h)) (@finite_arrow_tail_next (Functor_cat K C) (@OneCatNativeExactArrowPair K
  C (@additive_preadditive C Prod t Add) C1 t (@additive_terminal_object C Prod t Add) T0 P Q N) (succ (succ
  zero)) (@kernel_adjunction_family_func K C (@additive_preadditive C Prod t Add) t (@additive_terminal_object C
  Prod t Add) P (@transf_arrow_diagram_func K C B X b)) (@finite_arrow_tail_next (Functor_cat K C)
  (@OneCatNativeExactArrowPair K C (@additive_preadditive C Prod t Add) C1 t (@additive_terminal_object C Prod t
  Add) T0 P Q N) (succ (succ (succ zero))) (@kernel_adjunction_family_func K C (@additive_preadditive C Prod t
  Add) t (@additive_terminal_object C Prod t Add) P (@one_cat_native_snake_alpha_diagram K C
  (@additive_preadditive C Prod t Add) C1 t (@additive_terminal_object C Prod t Add) T0 P A B X D b c h))
  (@kernel_adjunction_family_func K C (@additive_preadditive C Prod t Add) t (@additive_terminal_object C Prod t
  Add) P (@transf_arrow_diagram_func K C B X b)) (@one_cat_native_snake_kernel_first K C (@additive_preadditive
  C Prod t Add) C1 t (@additive_terminal_object C Prod t Add) T0 P Q A B X D b c h)
  (@one_cat_native_snake_six_term_result K C C1 Prod t Add T0 P Q N A B X D b c h)) (@finite_arrow_tail_arrow
  (Functor_cat K C) (@OneCatNativeExactArrowPair K C (@additive_preadditive C Prod t Add) C1 t
  (@additive_terminal_object C Prod t Add) T0 P Q N) (succ (succ (succ zero))) (@kernel_adjunction_family_func K
  C (@additive_preadditive C Prod t Add) t (@additive_terminal_object C Prod t Add) P
  (@one_cat_native_snake_alpha_diagram K C (@additive_preadditive C Prod t Add) C1 t (@additive_terminal_object
  C Prod t Add) T0 P A B X D b c h)) (@kernel_adjunction_family_func K C (@additive_preadditive C Prod t Add) t
  (@additive_terminal_object C Prod t Add) P (@transf_arrow_diagram_func K C B X b))
  (@one_cat_native_snake_kernel_first K C (@additive_preadditive C Prod t Add) C1 t (@additive_terminal_object C
  Prod t Add) T0 P Q A B X D b c h) (@one_cat_native_snake_six_term_result K C C1 Prod t Add T0 P Q N A B X D b
  c h)) (@finite_arrow_tail_rest (Functor_cat K C) (@OneCatNativeExactArrowPair K C (@additive_preadditive C
  Prod t Add) C1 t (@additive_terminal_object C Prod t Add) T0 P Q N) (succ (succ (succ zero)))
  (@kernel_adjunction_family_func K C (@additive_preadditive C Prod t Add) t (@additive_terminal_object C Prod t
  Add) P (@one_cat_native_snake_alpha_diagram K C (@additive_preadditive C Prod t Add) C1 t
  (@additive_terminal_object C Prod t Add) T0 P A B X D b c h)) (@kernel_adjunction_family_func K C
  (@additive_preadditive C Prod t Add) t (@additive_terminal_object C Prod t Add) P (@transf_arrow_diagram_func
  K C B X b)) (@one_cat_native_snake_kernel_first K C (@additive_preadditive C Prod t Add) C1 t
  (@additive_terminal_object C Prod t Add) T0 P Q A B X D b c h) (@one_cat_native_snake_six_term_result K C C1
  Prod t Add T0 P Q N A B X D b c h))) (@finite_arrow_tail_arrow (Functor_cat K C) (@OneCatNativeExactArrowPair
  K C (@additive_preadditive C Prod t Add) C1 t (@additive_terminal_object C Prod t Add) T0 P Q N) (succ (succ
  zero)) (@kernel_adjunction_family_func K C (@additive_preadditive C Prod t Add) t (@additive_terminal_object C
  Prod t Add) P (@transf_arrow_diagram_func K C B X b)) (@finite_arrow_tail_next (Functor_cat K C)
  (@OneCatNativeExactArrowPair K C (@additive_preadditive C Prod t Add) C1 t (@additive_terminal_object C Prod t
  Add) T0 P Q N) (succ (succ (succ zero))) (@kernel_adjunction_family_func K C (@additive_preadditive C Prod t
  Add) t (@additive_terminal_object C Prod t Add) P (@one_cat_native_snake_alpha_diagram K C
  (@additive_preadditive C Prod t Add) C1 t (@additive_terminal_object C Prod t Add) T0 P A B X D b c h))
  (@kernel_adjunction_family_func K C (@additive_preadditive C Prod t Add) t (@additive_terminal_object C Prod t
  Add) P (@transf_arrow_diagram_func K C B X b)) (@one_cat_native_snake_kernel_first K C (@additive_preadditive
  C Prod t Add) C1 t (@additive_terminal_object C Prod t Add) T0 P Q A B X D b c h)
  (@one_cat_native_snake_six_term_result K C C1 Prod t Add T0 P Q N A B X D b c h)) (@finite_arrow_tail_arrow
  (Functor_cat K C) (@OneCatNativeExactArrowPair K C (@additive_preadditive C Prod t Add) C1 t
  (@additive_terminal_object C Prod t Add) T0 P Q N) (succ (succ (succ zero))) (@kernel_adjunction_family_func K
  C (@additive_preadditive C Prod t Add) t (@additive_terminal_object C Prod t Add) P
  (@one_cat_native_snake_alpha_diagram K C (@additive_preadditive C Prod t Add) C1 t (@additive_terminal_object
  C Prod t Add) T0 P A B X D b c h)) (@kernel_adjunction_family_func K C (@additive_preadditive C Prod t Add) t
  (@additive_terminal_object C Prod t Add) P (@transf_arrow_diagram_func K C B X b))
  (@one_cat_native_snake_kernel_first K C (@additive_preadditive C Prod t Add) C1 t (@additive_terminal_object C
  Prod t Add) T0 P Q A B X D b c h) (@one_cat_native_snake_six_term_result K C C1 Prod t Add T0 P Q N A B X D b
  c h)) (@finite_arrow_tail_rest (Functor_cat K C) (@OneCatNativeExactArrowPair K C (@additive_preadditive C
  Prod t Add) C1 t (@additive_terminal_object C Prod t Add) T0 P Q N) (succ (succ (succ zero)))
  (@kernel_adjunction_family_func K C (@additive_preadditive C Prod t Add) t (@additive_terminal_object C Prod t
  Add) P (@one_cat_native_snake_alpha_diagram K C (@additive_preadditive C Prod t Add) C1 t
  (@additive_terminal_object C Prod t Add) T0 P A B X D b c h)) (@kernel_adjunction_family_func K C
  (@additive_preadditive C Prod t Add) t (@additive_terminal_object C Prod t Add) P (@transf_arrow_diagram_func
  K C B X b)) (@one_cat_native_snake_kernel_first K C (@additive_preadditive C Prod t Add) C1 t
  (@additive_terminal_object C Prod t Add) T0 P Q A B X D b c h) (@one_cat_native_snake_six_term_result K C C1
  Prod t Add T0 P Q N A B X D b c h))) (@finite_arrow_tail_arrow (Functor_cat K C) (@OneCatNativeExactArrowPair
  K C (@additive_preadditive C Prod t Add) C1 t (@additive_terminal_object C Prod t Add) T0 P Q N) (succ (succ
  (succ zero))) (@kernel_adjunction_family_func K C (@additive_preadditive C Prod t Add) t
  (@additive_terminal_object C Prod t Add) P (@one_cat_native_snake_alpha_diagram K C (@additive_preadditive C
  Prod t Add) C1 t (@additive_terminal_object C Prod t Add) T0 P A B X D b c h)) (@kernel_adjunction_family_func
  K C (@additive_preadditive C Prod t Add) t (@additive_terminal_object C Prod t Add) P
  (@transf_arrow_diagram_func K C B X b)) (@one_cat_native_snake_kernel_first K C (@additive_preadditive C Prod
  t Add) C1 t (@additive_terminal_object C Prod t Add) T0 P Q A B X D b c h)
  (@one_cat_native_snake_six_term_result K C C1 Prod t Add T0 P Q N A B X D b c h)))
  (@zero_arrow_family_zero_transf K C t (@additive_terminal_object C Prod t Add) T0
  (@kernel_adjunction_family_func K C (@additive_preadditive C Prod t Add) t (@additive_terminal_object C Prod t
  Add) P (@transf_arrow_diagram_func K C B X b)) (@finite_arrow_tail_next (Functor_cat K C)
  (@OneCatNativeExactArrowPair K C (@additive_preadditive C Prod t Add) C1 t (@additive_terminal_object C Prod t
  Add) T0 P Q N) (succ (succ zero)) (@kernel_adjunction_family_func K C (@additive_preadditive C Prod t Add) t
  (@additive_terminal_object C Prod t Add) P (@transf_arrow_diagram_func K C B X b)) (@finite_arrow_tail_next
  (Functor_cat K C) (@OneCatNativeExactArrowPair K C (@additive_preadditive C Prod t Add) C1 t
  (@additive_terminal_object C Prod t Add) T0 P Q N) (succ (succ (succ zero))) (@kernel_adjunction_family_func K
  C (@additive_preadditive C Prod t Add) t (@additive_terminal_object C Prod t Add) P
  (@one_cat_native_snake_alpha_diagram K C (@additive_preadditive C Prod t Add) C1 t (@additive_terminal_object
  C Prod t Add) T0 P A B X D b c h)) (@kernel_adjunction_family_func K C (@additive_preadditive C Prod t Add) t
  (@additive_terminal_object C Prod t Add) P (@transf_arrow_diagram_func K C B X b))
  (@one_cat_native_snake_kernel_first K C (@additive_preadditive C Prod t Add) C1 t (@additive_terminal_object C
  Prod t Add) T0 P Q A B X D b c h) (@one_cat_native_snake_six_term_result K C C1 Prod t Add T0 P Q N A B X D b
  c h)) (@finite_arrow_tail_arrow (Functor_cat K C) (@OneCatNativeExactArrowPair K C (@additive_preadditive C
  Prod t Add) C1 t (@additive_terminal_object C Prod t Add) T0 P Q N) (succ (succ (succ zero)))
  (@kernel_adjunction_family_func K C (@additive_preadditive C Prod t Add) t (@additive_terminal_object C Prod t
  Add) P (@one_cat_native_snake_alpha_diagram K C (@additive_preadditive C Prod t Add) C1 t
  (@additive_terminal_object C Prod t Add) T0 P A B X D b c h)) (@kernel_adjunction_family_func K C
  (@additive_preadditive C Prod t Add) t (@additive_terminal_object C Prod t Add) P (@transf_arrow_diagram_func
  K C B X b)) (@one_cat_native_snake_kernel_first K C (@additive_preadditive C Prod t Add) C1 t
  (@additive_terminal_object C Prod t Add) T0 P Q A B X D b c h) (@one_cat_native_snake_six_term_result K C C1
  Prod t Add T0 P Q N A B X D b c h)) (@finite_arrow_tail_rest (Functor_cat K C) (@OneCatNativeExactArrowPair K
  C (@additive_preadditive C Prod t Add) C1 t (@additive_terminal_object C Prod t Add) T0 P Q N) (succ (succ
  (succ zero))) (@kernel_adjunction_family_func K C (@additive_preadditive C Prod t Add) t
  (@additive_terminal_object C Prod t Add) P (@one_cat_native_snake_alpha_diagram K C (@additive_preadditive C
  Prod t Add) C1 t (@additive_terminal_object C Prod t Add) T0 P A B X D b c h)) (@kernel_adjunction_family_func
  K C (@additive_preadditive C Prod t Add) t (@additive_terminal_object C Prod t Add) P
  (@transf_arrow_diagram_func K C B X b)) (@one_cat_native_snake_kernel_first K C (@additive_preadditive C Prod
  t Add) C1 t (@additive_terminal_object C Prod t Add) T0 P Q A B X D b c h)
  (@one_cat_native_snake_six_term_result K C C1 Prod t Add T0 P Q N A B X D b c h)))));

// The third annotation retains the original native input.
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
  ⊢ (@one_cat_native_exact_arrow_pair_input K C (@additive_preadditive C Prod t Add) C1 t
  (@additive_terminal_object C Prod t Add) T0 P Q N (@finite_arrow_tail_next (Functor_cat K C)
  (@OneCatNativeExactArrowPair K C (@additive_preadditive C Prod t Add) C1 t (@additive_terminal_object C Prod t
  Add) T0 P Q N) (succ (succ (succ zero))) (@kernel_adjunction_family_func K C (@additive_preadditive C Prod t
  Add) t (@additive_terminal_object C Prod t Add) P (@one_cat_native_snake_alpha_diagram K C
  (@additive_preadditive C Prod t Add) C1 t (@additive_terminal_object C Prod t Add) T0 P A B X D b c h))
  (@kernel_adjunction_family_func K C (@additive_preadditive C Prod t Add) t (@additive_terminal_object C Prod t
  Add) P (@transf_arrow_diagram_func K C B X b)) (@one_cat_native_snake_kernel_first K C (@additive_preadditive
  C Prod t Add) C1 t (@additive_terminal_object C Prod t Add) T0 P Q A B X D b c h)
  (@one_cat_native_snake_six_term_result K C C1 Prod t Add T0 P Q N A B X D b c h)) (@finite_arrow_tail_next
  (Functor_cat K C) (@OneCatNativeExactArrowPair K C (@additive_preadditive C Prod t Add) C1 t
  (@additive_terminal_object C Prod t Add) T0 P Q N) (succ (succ zero)) (@kernel_adjunction_family_func K C
  (@additive_preadditive C Prod t Add) t (@additive_terminal_object C Prod t Add) P (@transf_arrow_diagram_func
  K C B X b)) (@finite_arrow_tail_next (Functor_cat K C) (@OneCatNativeExactArrowPair K C (@additive_preadditive
  C Prod t Add) C1 t (@additive_terminal_object C Prod t Add) T0 P Q N) (succ (succ (succ zero)))
  (@kernel_adjunction_family_func K C (@additive_preadditive C Prod t Add) t (@additive_terminal_object C Prod t
  Add) P (@one_cat_native_snake_alpha_diagram K C (@additive_preadditive C Prod t Add) C1 t
  (@additive_terminal_object C Prod t Add) T0 P A B X D b c h)) (@kernel_adjunction_family_func K C
  (@additive_preadditive C Prod t Add) t (@additive_terminal_object C Prod t Add) P (@transf_arrow_diagram_func
  K C B X b)) (@one_cat_native_snake_kernel_first K C (@additive_preadditive C Prod t Add) C1 t
  (@additive_terminal_object C Prod t Add) T0 P Q A B X D b c h) (@one_cat_native_snake_six_term_result K C C1
  Prod t Add T0 P Q N A B X D b c h)) (@finite_arrow_tail_arrow (Functor_cat K C) (@OneCatNativeExactArrowPair K
  C (@additive_preadditive C Prod t Add) C1 t (@additive_terminal_object C Prod t Add) T0 P Q N) (succ (succ
  (succ zero))) (@kernel_adjunction_family_func K C (@additive_preadditive C Prod t Add) t
  (@additive_terminal_object C Prod t Add) P (@one_cat_native_snake_alpha_diagram K C (@additive_preadditive C
  Prod t Add) C1 t (@additive_terminal_object C Prod t Add) T0 P A B X D b c h)) (@kernel_adjunction_family_func
  K C (@additive_preadditive C Prod t Add) t (@additive_terminal_object C Prod t Add) P
  (@transf_arrow_diagram_func K C B X b)) (@one_cat_native_snake_kernel_first K C (@additive_preadditive C Prod
  t Add) C1 t (@additive_terminal_object C Prod t Add) T0 P Q A B X D b c h)
  (@one_cat_native_snake_six_term_result K C C1 Prod t Add T0 P Q N A B X D b c h)) (@finite_arrow_tail_rest
  (Functor_cat K C) (@OneCatNativeExactArrowPair K C (@additive_preadditive C Prod t Add) C1 t
  (@additive_terminal_object C Prod t Add) T0 P Q N) (succ (succ (succ zero))) (@kernel_adjunction_family_func K
  C (@additive_preadditive C Prod t Add) t (@additive_terminal_object C Prod t Add) P
  (@one_cat_native_snake_alpha_diagram K C (@additive_preadditive C Prod t Add) C1 t (@additive_terminal_object
  C Prod t Add) T0 P A B X D b c h)) (@kernel_adjunction_family_func K C (@additive_preadditive C Prod t Add) t
  (@additive_terminal_object C Prod t Add) P (@transf_arrow_diagram_func K C B X b))
  (@one_cat_native_snake_kernel_first K C (@additive_preadditive C Prod t Add) C1 t (@additive_terminal_object C
  Prod t Add) T0 P Q A B X D b c h) (@one_cat_native_snake_six_term_result K C C1 Prod t Add T0 P Q N A B X D b
  c h))) (@finite_arrow_tail_next (Functor_cat K C) (@OneCatNativeExactArrowPair K C (@additive_preadditive C
  Prod t Add) C1 t (@additive_terminal_object C Prod t Add) T0 P Q N) (succ zero) (@finite_arrow_tail_next
  (Functor_cat K C) (@OneCatNativeExactArrowPair K C (@additive_preadditive C Prod t Add) C1 t
  (@additive_terminal_object C Prod t Add) T0 P Q N) (succ (succ (succ zero))) (@kernel_adjunction_family_func K
  C (@additive_preadditive C Prod t Add) t (@additive_terminal_object C Prod t Add) P
  (@one_cat_native_snake_alpha_diagram K C (@additive_preadditive C Prod t Add) C1 t (@additive_terminal_object
  C Prod t Add) T0 P A B X D b c h)) (@kernel_adjunction_family_func K C (@additive_preadditive C Prod t Add) t
  (@additive_terminal_object C Prod t Add) P (@transf_arrow_diagram_func K C B X b))
  (@one_cat_native_snake_kernel_first K C (@additive_preadditive C Prod t Add) C1 t (@additive_terminal_object C
  Prod t Add) T0 P Q A B X D b c h) (@one_cat_native_snake_six_term_result K C C1 Prod t Add T0 P Q N A B X D b
  c h)) (@finite_arrow_tail_next (Functor_cat K C) (@OneCatNativeExactArrowPair K C (@additive_preadditive C
  Prod t Add) C1 t (@additive_terminal_object C Prod t Add) T0 P Q N) (succ (succ zero))
  (@kernel_adjunction_family_func K C (@additive_preadditive C Prod t Add) t (@additive_terminal_object C Prod t
  Add) P (@transf_arrow_diagram_func K C B X b)) (@finite_arrow_tail_next (Functor_cat K C)
  (@OneCatNativeExactArrowPair K C (@additive_preadditive C Prod t Add) C1 t (@additive_terminal_object C Prod t
  Add) T0 P Q N) (succ (succ (succ zero))) (@kernel_adjunction_family_func K C (@additive_preadditive C Prod t
  Add) t (@additive_terminal_object C Prod t Add) P (@one_cat_native_snake_alpha_diagram K C
  (@additive_preadditive C Prod t Add) C1 t (@additive_terminal_object C Prod t Add) T0 P A B X D b c h))
  (@kernel_adjunction_family_func K C (@additive_preadditive C Prod t Add) t (@additive_terminal_object C Prod t
  Add) P (@transf_arrow_diagram_func K C B X b)) (@one_cat_native_snake_kernel_first K C (@additive_preadditive
  C Prod t Add) C1 t (@additive_terminal_object C Prod t Add) T0 P Q A B X D b c h)
  (@one_cat_native_snake_six_term_result K C C1 Prod t Add T0 P Q N A B X D b c h)) (@finite_arrow_tail_arrow
  (Functor_cat K C) (@OneCatNativeExactArrowPair K C (@additive_preadditive C Prod t Add) C1 t
  (@additive_terminal_object C Prod t Add) T0 P Q N) (succ (succ (succ zero))) (@kernel_adjunction_family_func K
  C (@additive_preadditive C Prod t Add) t (@additive_terminal_object C Prod t Add) P
  (@one_cat_native_snake_alpha_diagram K C (@additive_preadditive C Prod t Add) C1 t (@additive_terminal_object
  C Prod t Add) T0 P A B X D b c h)) (@kernel_adjunction_family_func K C (@additive_preadditive C Prod t Add) t
  (@additive_terminal_object C Prod t Add) P (@transf_arrow_diagram_func K C B X b))
  (@one_cat_native_snake_kernel_first K C (@additive_preadditive C Prod t Add) C1 t (@additive_terminal_object C
  Prod t Add) T0 P Q A B X D b c h) (@one_cat_native_snake_six_term_result K C C1 Prod t Add T0 P Q N A B X D b
  c h)) (@finite_arrow_tail_rest (Functor_cat K C) (@OneCatNativeExactArrowPair K C (@additive_preadditive C
  Prod t Add) C1 t (@additive_terminal_object C Prod t Add) T0 P Q N) (succ (succ (succ zero)))
  (@kernel_adjunction_family_func K C (@additive_preadditive C Prod t Add) t (@additive_terminal_object C Prod t
  Add) P (@one_cat_native_snake_alpha_diagram K C (@additive_preadditive C Prod t Add) C1 t
  (@additive_terminal_object C Prod t Add) T0 P A B X D b c h)) (@kernel_adjunction_family_func K C
  (@additive_preadditive C Prod t Add) t (@additive_terminal_object C Prod t Add) P (@transf_arrow_diagram_func
  K C B X b)) (@one_cat_native_snake_kernel_first K C (@additive_preadditive C Prod t Add) C1 t
  (@additive_terminal_object C Prod t Add) T0 P Q A B X D b c h) (@one_cat_native_snake_six_term_result K C C1
  Prod t Add T0 P Q N A B X D b c h))) (@finite_arrow_tail_arrow (Functor_cat K C) (@OneCatNativeExactArrowPair
  K C (@additive_preadditive C Prod t Add) C1 t (@additive_terminal_object C Prod t Add) T0 P Q N) (succ (succ
  zero)) (@kernel_adjunction_family_func K C (@additive_preadditive C Prod t Add) t (@additive_terminal_object C
  Prod t Add) P (@transf_arrow_diagram_func K C B X b)) (@finite_arrow_tail_next (Functor_cat K C)
  (@OneCatNativeExactArrowPair K C (@additive_preadditive C Prod t Add) C1 t (@additive_terminal_object C Prod t
  Add) T0 P Q N) (succ (succ (succ zero))) (@kernel_adjunction_family_func K C (@additive_preadditive C Prod t
  Add) t (@additive_terminal_object C Prod t Add) P (@one_cat_native_snake_alpha_diagram K C
  (@additive_preadditive C Prod t Add) C1 t (@additive_terminal_object C Prod t Add) T0 P A B X D b c h))
  (@kernel_adjunction_family_func K C (@additive_preadditive C Prod t Add) t (@additive_terminal_object C Prod t
  Add) P (@transf_arrow_diagram_func K C B X b)) (@one_cat_native_snake_kernel_first K C (@additive_preadditive
  C Prod t Add) C1 t (@additive_terminal_object C Prod t Add) T0 P Q A B X D b c h)
  (@one_cat_native_snake_six_term_result K C C1 Prod t Add T0 P Q N A B X D b c h)) (@finite_arrow_tail_arrow
  (Functor_cat K C) (@OneCatNativeExactArrowPair K C (@additive_preadditive C Prod t Add) C1 t
  (@additive_terminal_object C Prod t Add) T0 P Q N) (succ (succ (succ zero))) (@kernel_adjunction_family_func K
  C (@additive_preadditive C Prod t Add) t (@additive_terminal_object C Prod t Add) P
  (@one_cat_native_snake_alpha_diagram K C (@additive_preadditive C Prod t Add) C1 t (@additive_terminal_object
  C Prod t Add) T0 P A B X D b c h)) (@kernel_adjunction_family_func K C (@additive_preadditive C Prod t Add) t
  (@additive_terminal_object C Prod t Add) P (@transf_arrow_diagram_func K C B X b))
  (@one_cat_native_snake_kernel_first K C (@additive_preadditive C Prod t Add) C1 t (@additive_terminal_object C
  Prod t Add) T0 P Q A B X D b c h) (@one_cat_native_snake_six_term_result K C C1 Prod t Add T0 P Q N A B X D b
  c h)) (@finite_arrow_tail_rest (Functor_cat K C) (@OneCatNativeExactArrowPair K C (@additive_preadditive C
  Prod t Add) C1 t (@additive_terminal_object C Prod t Add) T0 P Q N) (succ (succ (succ zero)))
  (@kernel_adjunction_family_func K C (@additive_preadditive C Prod t Add) t (@additive_terminal_object C Prod t
  Add) P (@one_cat_native_snake_alpha_diagram K C (@additive_preadditive C Prod t Add) C1 t
  (@additive_terminal_object C Prod t Add) T0 P A B X D b c h)) (@kernel_adjunction_family_func K C
  (@additive_preadditive C Prod t Add) t (@additive_terminal_object C Prod t Add) P (@transf_arrow_diagram_func
  K C B X b)) (@one_cat_native_snake_kernel_first K C (@additive_preadditive C Prod t Add) C1 t
  (@additive_terminal_object C Prod t Add) T0 P Q A B X D b c h) (@one_cat_native_snake_six_term_result K C C1
  Prod t Add T0 P Q N A B X D b c h))) (@finite_arrow_tail_rest (Functor_cat K C) (@OneCatNativeExactArrowPair K
  C (@additive_preadditive C Prod t Add) C1 t (@additive_terminal_object C Prod t Add) T0 P Q N) (succ (succ
  zero)) (@kernel_adjunction_family_func K C (@additive_preadditive C Prod t Add) t (@additive_terminal_object C
  Prod t Add) P (@transf_arrow_diagram_func K C B X b)) (@finite_arrow_tail_next (Functor_cat K C)
  (@OneCatNativeExactArrowPair K C (@additive_preadditive C Prod t Add) C1 t (@additive_terminal_object C Prod t
  Add) T0 P Q N) (succ (succ (succ zero))) (@kernel_adjunction_family_func K C (@additive_preadditive C Prod t
  Add) t (@additive_terminal_object C Prod t Add) P (@one_cat_native_snake_alpha_diagram K C
  (@additive_preadditive C Prod t Add) C1 t (@additive_terminal_object C Prod t Add) T0 P A B X D b c h))
  (@kernel_adjunction_family_func K C (@additive_preadditive C Prod t Add) t (@additive_terminal_object C Prod t
  Add) P (@transf_arrow_diagram_func K C B X b)) (@one_cat_native_snake_kernel_first K C (@additive_preadditive
  C Prod t Add) C1 t (@additive_terminal_object C Prod t Add) T0 P Q A B X D b c h)
  (@one_cat_native_snake_six_term_result K C C1 Prod t Add T0 P Q N A B X D b c h)) (@finite_arrow_tail_arrow
  (Functor_cat K C) (@OneCatNativeExactArrowPair K C (@additive_preadditive C Prod t Add) C1 t
  (@additive_terminal_object C Prod t Add) T0 P Q N) (succ (succ (succ zero))) (@kernel_adjunction_family_func K
  C (@additive_preadditive C Prod t Add) t (@additive_terminal_object C Prod t Add) P
  (@one_cat_native_snake_alpha_diagram K C (@additive_preadditive C Prod t Add) C1 t (@additive_terminal_object
  C Prod t Add) T0 P A B X D b c h)) (@kernel_adjunction_family_func K C (@additive_preadditive C Prod t Add) t
  (@additive_terminal_object C Prod t Add) P (@transf_arrow_diagram_func K C B X b))
  (@one_cat_native_snake_kernel_first K C (@additive_preadditive C Prod t Add) C1 t (@additive_terminal_object C
  Prod t Add) T0 P Q A B X D b c h) (@one_cat_native_snake_six_term_result K C C1 Prod t Add T0 P Q N A B X D b
  c h)) (@finite_arrow_tail_rest (Functor_cat K C) (@OneCatNativeExactArrowPair K C (@additive_preadditive C
  Prod t Add) C1 t (@additive_terminal_object C Prod t Add) T0 P Q N) (succ (succ (succ zero)))
  (@kernel_adjunction_family_func K C (@additive_preadditive C Prod t Add) t (@additive_terminal_object C Prod t
  Add) P (@one_cat_native_snake_alpha_diagram K C (@additive_preadditive C Prod t Add) C1 t
  (@additive_terminal_object C Prod t Add) T0 P A B X D b c h)) (@kernel_adjunction_family_func K C
  (@additive_preadditive C Prod t Add) t (@additive_terminal_object C Prod t Add) P (@transf_arrow_diagram_func
  K C B X b)) (@one_cat_native_snake_kernel_first K C (@additive_preadditive C Prod t Add) C1 t
  (@additive_terminal_object C Prod t Add) T0 P Q A B X D b c h) (@one_cat_native_snake_six_term_result K C C1
  Prod t Add T0 P Q N A B X D b c h)))) (@finite_arrow_tail_arrow (Functor_cat K C) (@OneCatNativeExactArrowPair
  K C (@additive_preadditive C Prod t Add) C1 t (@additive_terminal_object C Prod t Add) T0 P Q N) (succ (succ
  zero)) (@kernel_adjunction_family_func K C (@additive_preadditive C Prod t Add) t (@additive_terminal_object C
  Prod t Add) P (@transf_arrow_diagram_func K C B X b)) (@finite_arrow_tail_next (Functor_cat K C)
  (@OneCatNativeExactArrowPair K C (@additive_preadditive C Prod t Add) C1 t (@additive_terminal_object C Prod t
  Add) T0 P Q N) (succ (succ (succ zero))) (@kernel_adjunction_family_func K C (@additive_preadditive C Prod t
  Add) t (@additive_terminal_object C Prod t Add) P (@one_cat_native_snake_alpha_diagram K C
  (@additive_preadditive C Prod t Add) C1 t (@additive_terminal_object C Prod t Add) T0 P A B X D b c h))
  (@kernel_adjunction_family_func K C (@additive_preadditive C Prod t Add) t (@additive_terminal_object C Prod t
  Add) P (@transf_arrow_diagram_func K C B X b)) (@one_cat_native_snake_kernel_first K C (@additive_preadditive
  C Prod t Add) C1 t (@additive_terminal_object C Prod t Add) T0 P Q A B X D b c h)
  (@one_cat_native_snake_six_term_result K C C1 Prod t Add T0 P Q N A B X D b c h)) (@finite_arrow_tail_arrow
  (Functor_cat K C) (@OneCatNativeExactArrowPair K C (@additive_preadditive C Prod t Add) C1 t
  (@additive_terminal_object C Prod t Add) T0 P Q N) (succ (succ (succ zero))) (@kernel_adjunction_family_func K
  C (@additive_preadditive C Prod t Add) t (@additive_terminal_object C Prod t Add) P
  (@one_cat_native_snake_alpha_diagram K C (@additive_preadditive C Prod t Add) C1 t (@additive_terminal_object
  C Prod t Add) T0 P A B X D b c h)) (@kernel_adjunction_family_func K C (@additive_preadditive C Prod t Add) t
  (@additive_terminal_object C Prod t Add) P (@transf_arrow_diagram_func K C B X b))
  (@one_cat_native_snake_kernel_first K C (@additive_preadditive C Prod t Add) C1 t (@additive_terminal_object C
  Prod t Add) T0 P Q A B X D b c h) (@one_cat_native_snake_six_term_result K C C1 Prod t Add T0 P Q N A B X D b
  c h)) (@finite_arrow_tail_rest (Functor_cat K C) (@OneCatNativeExactArrowPair K C (@additive_preadditive C
  Prod t Add) C1 t (@additive_terminal_object C Prod t Add) T0 P Q N) (succ (succ (succ zero)))
  (@kernel_adjunction_family_func K C (@additive_preadditive C Prod t Add) t (@additive_terminal_object C Prod t
  Add) P (@one_cat_native_snake_alpha_diagram K C (@additive_preadditive C Prod t Add) C1 t
  (@additive_terminal_object C Prod t Add) T0 P A B X D b c h)) (@kernel_adjunction_family_func K C
  (@additive_preadditive C Prod t Add) t (@additive_terminal_object C Prod t Add) P (@transf_arrow_diagram_func
  K C B X b)) (@one_cat_native_snake_kernel_first K C (@additive_preadditive C Prod t Add) C1 t
  (@additive_terminal_object C Prod t Add) T0 P Q A B X D b c h) (@one_cat_native_snake_six_term_result K C C1
  Prod t Add T0 P Q N A B X D b c h))) (@finite_arrow_tail_arrow (Functor_cat K C) (@OneCatNativeExactArrowPair
  K C (@additive_preadditive C Prod t Add) C1 t (@additive_terminal_object C Prod t Add) T0 P Q N) (succ zero)
  (@finite_arrow_tail_next (Functor_cat K C) (@OneCatNativeExactArrowPair K C (@additive_preadditive C Prod t
  Add) C1 t (@additive_terminal_object C Prod t Add) T0 P Q N) (succ (succ (succ zero)))
  (@kernel_adjunction_family_func K C (@additive_preadditive C Prod t Add) t (@additive_terminal_object C Prod t
  Add) P (@one_cat_native_snake_alpha_diagram K C (@additive_preadditive C Prod t Add) C1 t
  (@additive_terminal_object C Prod t Add) T0 P A B X D b c h)) (@kernel_adjunction_family_func K C
  (@additive_preadditive C Prod t Add) t (@additive_terminal_object C Prod t Add) P (@transf_arrow_diagram_func
  K C B X b)) (@one_cat_native_snake_kernel_first K C (@additive_preadditive C Prod t Add) C1 t
  (@additive_terminal_object C Prod t Add) T0 P Q A B X D b c h) (@one_cat_native_snake_six_term_result K C C1
  Prod t Add T0 P Q N A B X D b c h)) (@finite_arrow_tail_next (Functor_cat K C) (@OneCatNativeExactArrowPair K
  C (@additive_preadditive C Prod t Add) C1 t (@additive_terminal_object C Prod t Add) T0 P Q N) (succ (succ
  zero)) (@kernel_adjunction_family_func K C (@additive_preadditive C Prod t Add) t (@additive_terminal_object C
  Prod t Add) P (@transf_arrow_diagram_func K C B X b)) (@finite_arrow_tail_next (Functor_cat K C)
  (@OneCatNativeExactArrowPair K C (@additive_preadditive C Prod t Add) C1 t (@additive_terminal_object C Prod t
  Add) T0 P Q N) (succ (succ (succ zero))) (@kernel_adjunction_family_func K C (@additive_preadditive C Prod t
  Add) t (@additive_terminal_object C Prod t Add) P (@one_cat_native_snake_alpha_diagram K C
  (@additive_preadditive C Prod t Add) C1 t (@additive_terminal_object C Prod t Add) T0 P A B X D b c h))
  (@kernel_adjunction_family_func K C (@additive_preadditive C Prod t Add) t (@additive_terminal_object C Prod t
  Add) P (@transf_arrow_diagram_func K C B X b)) (@one_cat_native_snake_kernel_first K C (@additive_preadditive
  C Prod t Add) C1 t (@additive_terminal_object C Prod t Add) T0 P Q A B X D b c h)
  (@one_cat_native_snake_six_term_result K C C1 Prod t Add T0 P Q N A B X D b c h)) (@finite_arrow_tail_arrow
  (Functor_cat K C) (@OneCatNativeExactArrowPair K C (@additive_preadditive C Prod t Add) C1 t
  (@additive_terminal_object C Prod t Add) T0 P Q N) (succ (succ (succ zero))) (@kernel_adjunction_family_func K
  C (@additive_preadditive C Prod t Add) t (@additive_terminal_object C Prod t Add) P
  (@one_cat_native_snake_alpha_diagram K C (@additive_preadditive C Prod t Add) C1 t (@additive_terminal_object
  C Prod t Add) T0 P A B X D b c h)) (@kernel_adjunction_family_func K C (@additive_preadditive C Prod t Add) t
  (@additive_terminal_object C Prod t Add) P (@transf_arrow_diagram_func K C B X b))
  (@one_cat_native_snake_kernel_first K C (@additive_preadditive C Prod t Add) C1 t (@additive_terminal_object C
  Prod t Add) T0 P Q A B X D b c h) (@one_cat_native_snake_six_term_result K C C1 Prod t Add T0 P Q N A B X D b
  c h)) (@finite_arrow_tail_rest (Functor_cat K C) (@OneCatNativeExactArrowPair K C (@additive_preadditive C
  Prod t Add) C1 t (@additive_terminal_object C Prod t Add) T0 P Q N) (succ (succ (succ zero)))
  (@kernel_adjunction_family_func K C (@additive_preadditive C Prod t Add) t (@additive_terminal_object C Prod t
  Add) P (@one_cat_native_snake_alpha_diagram K C (@additive_preadditive C Prod t Add) C1 t
  (@additive_terminal_object C Prod t Add) T0 P A B X D b c h)) (@kernel_adjunction_family_func K C
  (@additive_preadditive C Prod t Add) t (@additive_terminal_object C Prod t Add) P (@transf_arrow_diagram_func
  K C B X b)) (@one_cat_native_snake_kernel_first K C (@additive_preadditive C Prod t Add) C1 t
  (@additive_terminal_object C Prod t Add) T0 P Q A B X D b c h) (@one_cat_native_snake_six_term_result K C C1
  Prod t Add T0 P Q N A B X D b c h))) (@finite_arrow_tail_arrow (Functor_cat K C) (@OneCatNativeExactArrowPair
  K C (@additive_preadditive C Prod t Add) C1 t (@additive_terminal_object C Prod t Add) T0 P Q N) (succ (succ
  zero)) (@kernel_adjunction_family_func K C (@additive_preadditive C Prod t Add) t (@additive_terminal_object C
  Prod t Add) P (@transf_arrow_diagram_func K C B X b)) (@finite_arrow_tail_next (Functor_cat K C)
  (@OneCatNativeExactArrowPair K C (@additive_preadditive C Prod t Add) C1 t (@additive_terminal_object C Prod t
  Add) T0 P Q N) (succ (succ (succ zero))) (@kernel_adjunction_family_func K C (@additive_preadditive C Prod t
  Add) t (@additive_terminal_object C Prod t Add) P (@one_cat_native_snake_alpha_diagram K C
  (@additive_preadditive C Prod t Add) C1 t (@additive_terminal_object C Prod t Add) T0 P A B X D b c h))
  (@kernel_adjunction_family_func K C (@additive_preadditive C Prod t Add) t (@additive_terminal_object C Prod t
  Add) P (@transf_arrow_diagram_func K C B X b)) (@one_cat_native_snake_kernel_first K C (@additive_preadditive
  C Prod t Add) C1 t (@additive_terminal_object C Prod t Add) T0 P Q A B X D b c h)
  (@one_cat_native_snake_six_term_result K C C1 Prod t Add T0 P Q N A B X D b c h)) (@finite_arrow_tail_arrow
  (Functor_cat K C) (@OneCatNativeExactArrowPair K C (@additive_preadditive C Prod t Add) C1 t
  (@additive_terminal_object C Prod t Add) T0 P Q N) (succ (succ (succ zero))) (@kernel_adjunction_family_func K
  C (@additive_preadditive C Prod t Add) t (@additive_terminal_object C Prod t Add) P
  (@one_cat_native_snake_alpha_diagram K C (@additive_preadditive C Prod t Add) C1 t (@additive_terminal_object
  C Prod t Add) T0 P A B X D b c h)) (@kernel_adjunction_family_func K C (@additive_preadditive C Prod t Add) t
  (@additive_terminal_object C Prod t Add) P (@transf_arrow_diagram_func K C B X b))
  (@one_cat_native_snake_kernel_first K C (@additive_preadditive C Prod t Add) C1 t (@additive_terminal_object C
  Prod t Add) T0 P Q A B X D b c h) (@one_cat_native_snake_six_term_result K C C1 Prod t Add T0 P Q N A B X D b
  c h)) (@finite_arrow_tail_rest (Functor_cat K C) (@OneCatNativeExactArrowPair K C (@additive_preadditive C
  Prod t Add) C1 t (@additive_terminal_object C Prod t Add) T0 P Q N) (succ (succ (succ zero)))
  (@kernel_adjunction_family_func K C (@additive_preadditive C Prod t Add) t (@additive_terminal_object C Prod t
  Add) P (@one_cat_native_snake_alpha_diagram K C (@additive_preadditive C Prod t Add) C1 t
  (@additive_terminal_object C Prod t Add) T0 P A B X D b c h)) (@kernel_adjunction_family_func K C
  (@additive_preadditive C Prod t Add) t (@additive_terminal_object C Prod t Add) P (@transf_arrow_diagram_func
  K C B X b)) (@one_cat_native_snake_kernel_first K C (@additive_preadditive C Prod t Add) C1 t
  (@additive_terminal_object C Prod t Add) T0 P Q A B X D b c h) (@one_cat_native_snake_six_term_result K C C1
  Prod t Add T0 P Q N A B X D b c h))) (@finite_arrow_tail_rest (Functor_cat K C) (@OneCatNativeExactArrowPair K
  C (@additive_preadditive C Prod t Add) C1 t (@additive_terminal_object C Prod t Add) T0 P Q N) (succ (succ
  zero)) (@kernel_adjunction_family_func K C (@additive_preadditive C Prod t Add) t (@additive_terminal_object C
  Prod t Add) P (@transf_arrow_diagram_func K C B X b)) (@finite_arrow_tail_next (Functor_cat K C)
  (@OneCatNativeExactArrowPair K C (@additive_preadditive C Prod t Add) C1 t (@additive_terminal_object C Prod t
  Add) T0 P Q N) (succ (succ (succ zero))) (@kernel_adjunction_family_func K C (@additive_preadditive C Prod t
  Add) t (@additive_terminal_object C Prod t Add) P (@one_cat_native_snake_alpha_diagram K C
  (@additive_preadditive C Prod t Add) C1 t (@additive_terminal_object C Prod t Add) T0 P A B X D b c h))
  (@kernel_adjunction_family_func K C (@additive_preadditive C Prod t Add) t (@additive_terminal_object C Prod t
  Add) P (@transf_arrow_diagram_func K C B X b)) (@one_cat_native_snake_kernel_first K C (@additive_preadditive
  C Prod t Add) C1 t (@additive_terminal_object C Prod t Add) T0 P Q A B X D b c h)
  (@one_cat_native_snake_six_term_result K C C1 Prod t Add T0 P Q N A B X D b c h)) (@finite_arrow_tail_arrow
  (Functor_cat K C) (@OneCatNativeExactArrowPair K C (@additive_preadditive C Prod t Add) C1 t
  (@additive_terminal_object C Prod t Add) T0 P Q N) (succ (succ (succ zero))) (@kernel_adjunction_family_func K
  C (@additive_preadditive C Prod t Add) t (@additive_terminal_object C Prod t Add) P
  (@one_cat_native_snake_alpha_diagram K C (@additive_preadditive C Prod t Add) C1 t (@additive_terminal_object
  C Prod t Add) T0 P A B X D b c h)) (@kernel_adjunction_family_func K C (@additive_preadditive C Prod t Add) t
  (@additive_terminal_object C Prod t Add) P (@transf_arrow_diagram_func K C B X b))
  (@one_cat_native_snake_kernel_first K C (@additive_preadditive C Prod t Add) C1 t (@additive_terminal_object C
  Prod t Add) T0 P Q A B X D b c h) (@one_cat_native_snake_six_term_result K C C1 Prod t Add T0 P Q N A B X D b
  c h)) (@finite_arrow_tail_rest (Functor_cat K C) (@OneCatNativeExactArrowPair K C (@additive_preadditive C
  Prod t Add) C1 t (@additive_terminal_object C Prod t Add) T0 P Q N) (succ (succ (succ zero)))
  (@kernel_adjunction_family_func K C (@additive_preadditive C Prod t Add) t (@additive_terminal_object C Prod t
  Add) P (@one_cat_native_snake_alpha_diagram K C (@additive_preadditive C Prod t Add) C1 t
  (@additive_terminal_object C Prod t Add) T0 P A B X D b c h)) (@kernel_adjunction_family_func K C
  (@additive_preadditive C Prod t Add) t (@additive_terminal_object C Prod t Add) P (@transf_arrow_diagram_func
  K C B X b)) (@one_cat_native_snake_kernel_first K C (@additive_preadditive C Prod t Add) C1 t
  (@additive_terminal_object C Prod t Add) T0 P Q A B X D b c h) (@one_cat_native_snake_six_term_result K C C1
  Prod t Add T0 P Q N A B X D b c h)))) (@finite_arrow_tail_step (Functor_cat K C) (@OneCatNativeExactArrowPair
  K C (@additive_preadditive C Prod t Add) C1 t (@additive_terminal_object C Prod t Add) T0 P Q N) (succ zero)
  (@finite_arrow_tail_next (Functor_cat K C) (@OneCatNativeExactArrowPair K C (@additive_preadditive C Prod t
  Add) C1 t (@additive_terminal_object C Prod t Add) T0 P Q N) (succ (succ (succ zero)))
  (@kernel_adjunction_family_func K C (@additive_preadditive C Prod t Add) t (@additive_terminal_object C Prod t
  Add) P (@one_cat_native_snake_alpha_diagram K C (@additive_preadditive C Prod t Add) C1 t
  (@additive_terminal_object C Prod t Add) T0 P A B X D b c h)) (@kernel_adjunction_family_func K C
  (@additive_preadditive C Prod t Add) t (@additive_terminal_object C Prod t Add) P (@transf_arrow_diagram_func
  K C B X b)) (@one_cat_native_snake_kernel_first K C (@additive_preadditive C Prod t Add) C1 t
  (@additive_terminal_object C Prod t Add) T0 P Q A B X D b c h) (@one_cat_native_snake_six_term_result K C C1
  Prod t Add T0 P Q N A B X D b c h)) (@finite_arrow_tail_next (Functor_cat K C) (@OneCatNativeExactArrowPair K
  C (@additive_preadditive C Prod t Add) C1 t (@additive_terminal_object C Prod t Add) T0 P Q N) (succ (succ
  zero)) (@kernel_adjunction_family_func K C (@additive_preadditive C Prod t Add) t (@additive_terminal_object C
  Prod t Add) P (@transf_arrow_diagram_func K C B X b)) (@finite_arrow_tail_next (Functor_cat K C)
  (@OneCatNativeExactArrowPair K C (@additive_preadditive C Prod t Add) C1 t (@additive_terminal_object C Prod t
  Add) T0 P Q N) (succ (succ (succ zero))) (@kernel_adjunction_family_func K C (@additive_preadditive C Prod t
  Add) t (@additive_terminal_object C Prod t Add) P (@one_cat_native_snake_alpha_diagram K C
  (@additive_preadditive C Prod t Add) C1 t (@additive_terminal_object C Prod t Add) T0 P A B X D b c h))
  (@kernel_adjunction_family_func K C (@additive_preadditive C Prod t Add) t (@additive_terminal_object C Prod t
  Add) P (@transf_arrow_diagram_func K C B X b)) (@one_cat_native_snake_kernel_first K C (@additive_preadditive
  C Prod t Add) C1 t (@additive_terminal_object C Prod t Add) T0 P Q A B X D b c h)
  (@one_cat_native_snake_six_term_result K C C1 Prod t Add T0 P Q N A B X D b c h)) (@finite_arrow_tail_arrow
  (Functor_cat K C) (@OneCatNativeExactArrowPair K C (@additive_preadditive C Prod t Add) C1 t
  (@additive_terminal_object C Prod t Add) T0 P Q N) (succ (succ (succ zero))) (@kernel_adjunction_family_func K
  C (@additive_preadditive C Prod t Add) t (@additive_terminal_object C Prod t Add) P
  (@one_cat_native_snake_alpha_diagram K C (@additive_preadditive C Prod t Add) C1 t (@additive_terminal_object
  C Prod t Add) T0 P A B X D b c h)) (@kernel_adjunction_family_func K C (@additive_preadditive C Prod t Add) t
  (@additive_terminal_object C Prod t Add) P (@transf_arrow_diagram_func K C B X b))
  (@one_cat_native_snake_kernel_first K C (@additive_preadditive C Prod t Add) C1 t (@additive_terminal_object C
  Prod t Add) T0 P Q A B X D b c h) (@one_cat_native_snake_six_term_result K C C1 Prod t Add T0 P Q N A B X D b
  c h)) (@finite_arrow_tail_rest (Functor_cat K C) (@OneCatNativeExactArrowPair K C (@additive_preadditive C
  Prod t Add) C1 t (@additive_terminal_object C Prod t Add) T0 P Q N) (succ (succ (succ zero)))
  (@kernel_adjunction_family_func K C (@additive_preadditive C Prod t Add) t (@additive_terminal_object C Prod t
  Add) P (@one_cat_native_snake_alpha_diagram K C (@additive_preadditive C Prod t Add) C1 t
  (@additive_terminal_object C Prod t Add) T0 P A B X D b c h)) (@kernel_adjunction_family_func K C
  (@additive_preadditive C Prod t Add) t (@additive_terminal_object C Prod t Add) P (@transf_arrow_diagram_func
  K C B X b)) (@one_cat_native_snake_kernel_first K C (@additive_preadditive C Prod t Add) C1 t
  (@additive_terminal_object C Prod t Add) T0 P Q A B X D b c h) (@one_cat_native_snake_six_term_result K C C1
  Prod t Add T0 P Q N A B X D b c h))) (@finite_arrow_tail_arrow (Functor_cat K C) (@OneCatNativeExactArrowPair
  K C (@additive_preadditive C Prod t Add) C1 t (@additive_terminal_object C Prod t Add) T0 P Q N) (succ (succ
  zero)) (@kernel_adjunction_family_func K C (@additive_preadditive C Prod t Add) t (@additive_terminal_object C
  Prod t Add) P (@transf_arrow_diagram_func K C B X b)) (@finite_arrow_tail_next (Functor_cat K C)
  (@OneCatNativeExactArrowPair K C (@additive_preadditive C Prod t Add) C1 t (@additive_terminal_object C Prod t
  Add) T0 P Q N) (succ (succ (succ zero))) (@kernel_adjunction_family_func K C (@additive_preadditive C Prod t
  Add) t (@additive_terminal_object C Prod t Add) P (@one_cat_native_snake_alpha_diagram K C
  (@additive_preadditive C Prod t Add) C1 t (@additive_terminal_object C Prod t Add) T0 P A B X D b c h))
  (@kernel_adjunction_family_func K C (@additive_preadditive C Prod t Add) t (@additive_terminal_object C Prod t
  Add) P (@transf_arrow_diagram_func K C B X b)) (@one_cat_native_snake_kernel_first K C (@additive_preadditive
  C Prod t Add) C1 t (@additive_terminal_object C Prod t Add) T0 P Q A B X D b c h)
  (@one_cat_native_snake_six_term_result K C C1 Prod t Add T0 P Q N A B X D b c h)) (@finite_arrow_tail_arrow
  (Functor_cat K C) (@OneCatNativeExactArrowPair K C (@additive_preadditive C Prod t Add) C1 t
  (@additive_terminal_object C Prod t Add) T0 P Q N) (succ (succ (succ zero))) (@kernel_adjunction_family_func K
  C (@additive_preadditive C Prod t Add) t (@additive_terminal_object C Prod t Add) P
  (@one_cat_native_snake_alpha_diagram K C (@additive_preadditive C Prod t Add) C1 t (@additive_terminal_object
  C Prod t Add) T0 P A B X D b c h)) (@kernel_adjunction_family_func K C (@additive_preadditive C Prod t Add) t
  (@additive_terminal_object C Prod t Add) P (@transf_arrow_diagram_func K C B X b))
  (@one_cat_native_snake_kernel_first K C (@additive_preadditive C Prod t Add) C1 t (@additive_terminal_object C
  Prod t Add) T0 P Q A B X D b c h) (@one_cat_native_snake_six_term_result K C C1 Prod t Add T0 P Q N A B X D b
  c h)) (@finite_arrow_tail_rest (Functor_cat K C) (@OneCatNativeExactArrowPair K C (@additive_preadditive C
  Prod t Add) C1 t (@additive_terminal_object C Prod t Add) T0 P Q N) (succ (succ (succ zero)))
  (@kernel_adjunction_family_func K C (@additive_preadditive C Prod t Add) t (@additive_terminal_object C Prod t
  Add) P (@one_cat_native_snake_alpha_diagram K C (@additive_preadditive C Prod t Add) C1 t
  (@additive_terminal_object C Prod t Add) T0 P A B X D b c h)) (@kernel_adjunction_family_func K C
  (@additive_preadditive C Prod t Add) t (@additive_terminal_object C Prod t Add) P (@transf_arrow_diagram_func
  K C B X b)) (@one_cat_native_snake_kernel_first K C (@additive_preadditive C Prod t Add) C1 t
  (@additive_terminal_object C Prod t Add) T0 P Q A B X D b c h) (@one_cat_native_snake_six_term_result K C C1
  Prod t Add T0 P Q N A B X D b c h))) (@finite_arrow_tail_rest (Functor_cat K C) (@OneCatNativeExactArrowPair K
  C (@additive_preadditive C Prod t Add) C1 t (@additive_terminal_object C Prod t Add) T0 P Q N) (succ (succ
  zero)) (@kernel_adjunction_family_func K C (@additive_preadditive C Prod t Add) t (@additive_terminal_object C
  Prod t Add) P (@transf_arrow_diagram_func K C B X b)) (@finite_arrow_tail_next (Functor_cat K C)
  (@OneCatNativeExactArrowPair K C (@additive_preadditive C Prod t Add) C1 t (@additive_terminal_object C Prod t
  Add) T0 P Q N) (succ (succ (succ zero))) (@kernel_adjunction_family_func K C (@additive_preadditive C Prod t
  Add) t (@additive_terminal_object C Prod t Add) P (@one_cat_native_snake_alpha_diagram K C
  (@additive_preadditive C Prod t Add) C1 t (@additive_terminal_object C Prod t Add) T0 P A B X D b c h))
  (@kernel_adjunction_family_func K C (@additive_preadditive C Prod t Add) t (@additive_terminal_object C Prod t
  Add) P (@transf_arrow_diagram_func K C B X b)) (@one_cat_native_snake_kernel_first K C (@additive_preadditive
  C Prod t Add) C1 t (@additive_terminal_object C Prod t Add) T0 P Q A B X D b c h)
  (@one_cat_native_snake_six_term_result K C C1 Prod t Add T0 P Q N A B X D b c h)) (@finite_arrow_tail_arrow
  (Functor_cat K C) (@OneCatNativeExactArrowPair K C (@additive_preadditive C Prod t Add) C1 t
  (@additive_terminal_object C Prod t Add) T0 P Q N) (succ (succ (succ zero))) (@kernel_adjunction_family_func K
  C (@additive_preadditive C Prod t Add) t (@additive_terminal_object C Prod t Add) P
  (@one_cat_native_snake_alpha_diagram K C (@additive_preadditive C Prod t Add) C1 t (@additive_terminal_object
  C Prod t Add) T0 P A B X D b c h)) (@kernel_adjunction_family_func K C (@additive_preadditive C Prod t Add) t
  (@additive_terminal_object C Prod t Add) P (@transf_arrow_diagram_func K C B X b))
  (@one_cat_native_snake_kernel_first K C (@additive_preadditive C Prod t Add) C1 t (@additive_terminal_object C
  Prod t Add) T0 P Q A B X D b c h) (@one_cat_native_snake_six_term_result K C C1 Prod t Add T0 P Q N A B X D b
  c h)) (@finite_arrow_tail_rest (Functor_cat K C) (@OneCatNativeExactArrowPair K C (@additive_preadditive C
  Prod t Add) C1 t (@additive_terminal_object C Prod t Add) T0 P Q N) (succ (succ (succ zero)))
  (@kernel_adjunction_family_func K C (@additive_preadditive C Prod t Add) t (@additive_terminal_object C Prod t
  Add) P (@one_cat_native_snake_alpha_diagram K C (@additive_preadditive C Prod t Add) C1 t
  (@additive_terminal_object C Prod t Add) T0 P A B X D b c h)) (@kernel_adjunction_family_func K C
  (@additive_preadditive C Prod t Add) t (@additive_terminal_object C Prod t Add) P (@transf_arrow_diagram_func
  K C B X b)) (@one_cat_native_snake_kernel_first K C (@additive_preadditive C Prod t Add) C1 t
  (@additive_terminal_object C Prod t Add) T0 P Q A B X D b c h) (@one_cat_native_snake_six_term_result K C C1
  Prod t Add T0 P Q N A B X D b c h))))) ≡ (@one_cat_native_snake_third_exact_input K C C1 Prod t Add T0 P Q N A
  B X D b c h);

// The actual stored pair has its derived whole zero composite.
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
  ⊢ (@one_cat_native_exact_arrow_pair_zero K C (@additive_preadditive C Prod t Add) C1 t
  (@additive_terminal_object C Prod t Add) T0 P Q N (@finite_arrow_tail_next (Functor_cat K C)
  (@OneCatNativeExactArrowPair K C (@additive_preadditive C Prod t Add) C1 t (@additive_terminal_object C Prod t
  Add) T0 P Q N) (succ (succ (succ zero))) (@kernel_adjunction_family_func K C (@additive_preadditive C Prod t
  Add) t (@additive_terminal_object C Prod t Add) P (@one_cat_native_snake_alpha_diagram K C
  (@additive_preadditive C Prod t Add) C1 t (@additive_terminal_object C Prod t Add) T0 P A B X D b c h))
  (@kernel_adjunction_family_func K C (@additive_preadditive C Prod t Add) t (@additive_terminal_object C Prod t
  Add) P (@transf_arrow_diagram_func K C B X b)) (@one_cat_native_snake_kernel_first K C (@additive_preadditive
  C Prod t Add) C1 t (@additive_terminal_object C Prod t Add) T0 P Q A B X D b c h)
  (@one_cat_native_snake_six_term_result K C C1 Prod t Add T0 P Q N A B X D b c h)) (@finite_arrow_tail_next
  (Functor_cat K C) (@OneCatNativeExactArrowPair K C (@additive_preadditive C Prod t Add) C1 t
  (@additive_terminal_object C Prod t Add) T0 P Q N) (succ (succ zero)) (@kernel_adjunction_family_func K C
  (@additive_preadditive C Prod t Add) t (@additive_terminal_object C Prod t Add) P (@transf_arrow_diagram_func
  K C B X b)) (@finite_arrow_tail_next (Functor_cat K C) (@OneCatNativeExactArrowPair K C (@additive_preadditive
  C Prod t Add) C1 t (@additive_terminal_object C Prod t Add) T0 P Q N) (succ (succ (succ zero)))
  (@kernel_adjunction_family_func K C (@additive_preadditive C Prod t Add) t (@additive_terminal_object C Prod t
  Add) P (@one_cat_native_snake_alpha_diagram K C (@additive_preadditive C Prod t Add) C1 t
  (@additive_terminal_object C Prod t Add) T0 P A B X D b c h)) (@kernel_adjunction_family_func K C
  (@additive_preadditive C Prod t Add) t (@additive_terminal_object C Prod t Add) P (@transf_arrow_diagram_func
  K C B X b)) (@one_cat_native_snake_kernel_first K C (@additive_preadditive C Prod t Add) C1 t
  (@additive_terminal_object C Prod t Add) T0 P Q A B X D b c h) (@one_cat_native_snake_six_term_result K C C1
  Prod t Add T0 P Q N A B X D b c h)) (@finite_arrow_tail_arrow (Functor_cat K C) (@OneCatNativeExactArrowPair K
  C (@additive_preadditive C Prod t Add) C1 t (@additive_terminal_object C Prod t Add) T0 P Q N) (succ (succ
  (succ zero))) (@kernel_adjunction_family_func K C (@additive_preadditive C Prod t Add) t
  (@additive_terminal_object C Prod t Add) P (@one_cat_native_snake_alpha_diagram K C (@additive_preadditive C
  Prod t Add) C1 t (@additive_terminal_object C Prod t Add) T0 P A B X D b c h)) (@kernel_adjunction_family_func
  K C (@additive_preadditive C Prod t Add) t (@additive_terminal_object C Prod t Add) P
  (@transf_arrow_diagram_func K C B X b)) (@one_cat_native_snake_kernel_first K C (@additive_preadditive C Prod
  t Add) C1 t (@additive_terminal_object C Prod t Add) T0 P Q A B X D b c h)
  (@one_cat_native_snake_six_term_result K C C1 Prod t Add T0 P Q N A B X D b c h)) (@finite_arrow_tail_rest
  (Functor_cat K C) (@OneCatNativeExactArrowPair K C (@additive_preadditive C Prod t Add) C1 t
  (@additive_terminal_object C Prod t Add) T0 P Q N) (succ (succ (succ zero))) (@kernel_adjunction_family_func K
  C (@additive_preadditive C Prod t Add) t (@additive_terminal_object C Prod t Add) P
  (@one_cat_native_snake_alpha_diagram K C (@additive_preadditive C Prod t Add) C1 t (@additive_terminal_object
  C Prod t Add) T0 P A B X D b c h)) (@kernel_adjunction_family_func K C (@additive_preadditive C Prod t Add) t
  (@additive_terminal_object C Prod t Add) P (@transf_arrow_diagram_func K C B X b))
  (@one_cat_native_snake_kernel_first K C (@additive_preadditive C Prod t Add) C1 t (@additive_terminal_object C
  Prod t Add) T0 P Q A B X D b c h) (@one_cat_native_snake_six_term_result K C C1 Prod t Add T0 P Q N A B X D b
  c h))) (@finite_arrow_tail_next (Functor_cat K C) (@OneCatNativeExactArrowPair K C (@additive_preadditive C
  Prod t Add) C1 t (@additive_terminal_object C Prod t Add) T0 P Q N) (succ zero) (@finite_arrow_tail_next
  (Functor_cat K C) (@OneCatNativeExactArrowPair K C (@additive_preadditive C Prod t Add) C1 t
  (@additive_terminal_object C Prod t Add) T0 P Q N) (succ (succ (succ zero))) (@kernel_adjunction_family_func K
  C (@additive_preadditive C Prod t Add) t (@additive_terminal_object C Prod t Add) P
  (@one_cat_native_snake_alpha_diagram K C (@additive_preadditive C Prod t Add) C1 t (@additive_terminal_object
  C Prod t Add) T0 P A B X D b c h)) (@kernel_adjunction_family_func K C (@additive_preadditive C Prod t Add) t
  (@additive_terminal_object C Prod t Add) P (@transf_arrow_diagram_func K C B X b))
  (@one_cat_native_snake_kernel_first K C (@additive_preadditive C Prod t Add) C1 t (@additive_terminal_object C
  Prod t Add) T0 P Q A B X D b c h) (@one_cat_native_snake_six_term_result K C C1 Prod t Add T0 P Q N A B X D b
  c h)) (@finite_arrow_tail_next (Functor_cat K C) (@OneCatNativeExactArrowPair K C (@additive_preadditive C
  Prod t Add) C1 t (@additive_terminal_object C Prod t Add) T0 P Q N) (succ (succ zero))
  (@kernel_adjunction_family_func K C (@additive_preadditive C Prod t Add) t (@additive_terminal_object C Prod t
  Add) P (@transf_arrow_diagram_func K C B X b)) (@finite_arrow_tail_next (Functor_cat K C)
  (@OneCatNativeExactArrowPair K C (@additive_preadditive C Prod t Add) C1 t (@additive_terminal_object C Prod t
  Add) T0 P Q N) (succ (succ (succ zero))) (@kernel_adjunction_family_func K C (@additive_preadditive C Prod t
  Add) t (@additive_terminal_object C Prod t Add) P (@one_cat_native_snake_alpha_diagram K C
  (@additive_preadditive C Prod t Add) C1 t (@additive_terminal_object C Prod t Add) T0 P A B X D b c h))
  (@kernel_adjunction_family_func K C (@additive_preadditive C Prod t Add) t (@additive_terminal_object C Prod t
  Add) P (@transf_arrow_diagram_func K C B X b)) (@one_cat_native_snake_kernel_first K C (@additive_preadditive
  C Prod t Add) C1 t (@additive_terminal_object C Prod t Add) T0 P Q A B X D b c h)
  (@one_cat_native_snake_six_term_result K C C1 Prod t Add T0 P Q N A B X D b c h)) (@finite_arrow_tail_arrow
  (Functor_cat K C) (@OneCatNativeExactArrowPair K C (@additive_preadditive C Prod t Add) C1 t
  (@additive_terminal_object C Prod t Add) T0 P Q N) (succ (succ (succ zero))) (@kernel_adjunction_family_func K
  C (@additive_preadditive C Prod t Add) t (@additive_terminal_object C Prod t Add) P
  (@one_cat_native_snake_alpha_diagram K C (@additive_preadditive C Prod t Add) C1 t (@additive_terminal_object
  C Prod t Add) T0 P A B X D b c h)) (@kernel_adjunction_family_func K C (@additive_preadditive C Prod t Add) t
  (@additive_terminal_object C Prod t Add) P (@transf_arrow_diagram_func K C B X b))
  (@one_cat_native_snake_kernel_first K C (@additive_preadditive C Prod t Add) C1 t (@additive_terminal_object C
  Prod t Add) T0 P Q A B X D b c h) (@one_cat_native_snake_six_term_result K C C1 Prod t Add T0 P Q N A B X D b
  c h)) (@finite_arrow_tail_rest (Functor_cat K C) (@OneCatNativeExactArrowPair K C (@additive_preadditive C
  Prod t Add) C1 t (@additive_terminal_object C Prod t Add) T0 P Q N) (succ (succ (succ zero)))
  (@kernel_adjunction_family_func K C (@additive_preadditive C Prod t Add) t (@additive_terminal_object C Prod t
  Add) P (@one_cat_native_snake_alpha_diagram K C (@additive_preadditive C Prod t Add) C1 t
  (@additive_terminal_object C Prod t Add) T0 P A B X D b c h)) (@kernel_adjunction_family_func K C
  (@additive_preadditive C Prod t Add) t (@additive_terminal_object C Prod t Add) P (@transf_arrow_diagram_func
  K C B X b)) (@one_cat_native_snake_kernel_first K C (@additive_preadditive C Prod t Add) C1 t
  (@additive_terminal_object C Prod t Add) T0 P Q A B X D b c h) (@one_cat_native_snake_six_term_result K C C1
  Prod t Add T0 P Q N A B X D b c h))) (@finite_arrow_tail_arrow (Functor_cat K C) (@OneCatNativeExactArrowPair
  K C (@additive_preadditive C Prod t Add) C1 t (@additive_terminal_object C Prod t Add) T0 P Q N) (succ (succ
  zero)) (@kernel_adjunction_family_func K C (@additive_preadditive C Prod t Add) t (@additive_terminal_object C
  Prod t Add) P (@transf_arrow_diagram_func K C B X b)) (@finite_arrow_tail_next (Functor_cat K C)
  (@OneCatNativeExactArrowPair K C (@additive_preadditive C Prod t Add) C1 t (@additive_terminal_object C Prod t
  Add) T0 P Q N) (succ (succ (succ zero))) (@kernel_adjunction_family_func K C (@additive_preadditive C Prod t
  Add) t (@additive_terminal_object C Prod t Add) P (@one_cat_native_snake_alpha_diagram K C
  (@additive_preadditive C Prod t Add) C1 t (@additive_terminal_object C Prod t Add) T0 P A B X D b c h))
  (@kernel_adjunction_family_func K C (@additive_preadditive C Prod t Add) t (@additive_terminal_object C Prod t
  Add) P (@transf_arrow_diagram_func K C B X b)) (@one_cat_native_snake_kernel_first K C (@additive_preadditive
  C Prod t Add) C1 t (@additive_terminal_object C Prod t Add) T0 P Q A B X D b c h)
  (@one_cat_native_snake_six_term_result K C C1 Prod t Add T0 P Q N A B X D b c h)) (@finite_arrow_tail_arrow
  (Functor_cat K C) (@OneCatNativeExactArrowPair K C (@additive_preadditive C Prod t Add) C1 t
  (@additive_terminal_object C Prod t Add) T0 P Q N) (succ (succ (succ zero))) (@kernel_adjunction_family_func K
  C (@additive_preadditive C Prod t Add) t (@additive_terminal_object C Prod t Add) P
  (@one_cat_native_snake_alpha_diagram K C (@additive_preadditive C Prod t Add) C1 t (@additive_terminal_object
  C Prod t Add) T0 P A B X D b c h)) (@kernel_adjunction_family_func K C (@additive_preadditive C Prod t Add) t
  (@additive_terminal_object C Prod t Add) P (@transf_arrow_diagram_func K C B X b))
  (@one_cat_native_snake_kernel_first K C (@additive_preadditive C Prod t Add) C1 t (@additive_terminal_object C
  Prod t Add) T0 P Q A B X D b c h) (@one_cat_native_snake_six_term_result K C C1 Prod t Add T0 P Q N A B X D b
  c h)) (@finite_arrow_tail_rest (Functor_cat K C) (@OneCatNativeExactArrowPair K C (@additive_preadditive C
  Prod t Add) C1 t (@additive_terminal_object C Prod t Add) T0 P Q N) (succ (succ (succ zero)))
  (@kernel_adjunction_family_func K C (@additive_preadditive C Prod t Add) t (@additive_terminal_object C Prod t
  Add) P (@one_cat_native_snake_alpha_diagram K C (@additive_preadditive C Prod t Add) C1 t
  (@additive_terminal_object C Prod t Add) T0 P A B X D b c h)) (@kernel_adjunction_family_func K C
  (@additive_preadditive C Prod t Add) t (@additive_terminal_object C Prod t Add) P (@transf_arrow_diagram_func
  K C B X b)) (@one_cat_native_snake_kernel_first K C (@additive_preadditive C Prod t Add) C1 t
  (@additive_terminal_object C Prod t Add) T0 P Q A B X D b c h) (@one_cat_native_snake_six_term_result K C C1
  Prod t Add T0 P Q N A B X D b c h))) (@finite_arrow_tail_rest (Functor_cat K C) (@OneCatNativeExactArrowPair K
  C (@additive_preadditive C Prod t Add) C1 t (@additive_terminal_object C Prod t Add) T0 P Q N) (succ (succ
  zero)) (@kernel_adjunction_family_func K C (@additive_preadditive C Prod t Add) t (@additive_terminal_object C
  Prod t Add) P (@transf_arrow_diagram_func K C B X b)) (@finite_arrow_tail_next (Functor_cat K C)
  (@OneCatNativeExactArrowPair K C (@additive_preadditive C Prod t Add) C1 t (@additive_terminal_object C Prod t
  Add) T0 P Q N) (succ (succ (succ zero))) (@kernel_adjunction_family_func K C (@additive_preadditive C Prod t
  Add) t (@additive_terminal_object C Prod t Add) P (@one_cat_native_snake_alpha_diagram K C
  (@additive_preadditive C Prod t Add) C1 t (@additive_terminal_object C Prod t Add) T0 P A B X D b c h))
  (@kernel_adjunction_family_func K C (@additive_preadditive C Prod t Add) t (@additive_terminal_object C Prod t
  Add) P (@transf_arrow_diagram_func K C B X b)) (@one_cat_native_snake_kernel_first K C (@additive_preadditive
  C Prod t Add) C1 t (@additive_terminal_object C Prod t Add) T0 P Q A B X D b c h)
  (@one_cat_native_snake_six_term_result K C C1 Prod t Add T0 P Q N A B X D b c h)) (@finite_arrow_tail_arrow
  (Functor_cat K C) (@OneCatNativeExactArrowPair K C (@additive_preadditive C Prod t Add) C1 t
  (@additive_terminal_object C Prod t Add) T0 P Q N) (succ (succ (succ zero))) (@kernel_adjunction_family_func K
  C (@additive_preadditive C Prod t Add) t (@additive_terminal_object C Prod t Add) P
  (@one_cat_native_snake_alpha_diagram K C (@additive_preadditive C Prod t Add) C1 t (@additive_terminal_object
  C Prod t Add) T0 P A B X D b c h)) (@kernel_adjunction_family_func K C (@additive_preadditive C Prod t Add) t
  (@additive_terminal_object C Prod t Add) P (@transf_arrow_diagram_func K C B X b))
  (@one_cat_native_snake_kernel_first K C (@additive_preadditive C Prod t Add) C1 t (@additive_terminal_object C
  Prod t Add) T0 P Q A B X D b c h) (@one_cat_native_snake_six_term_result K C C1 Prod t Add T0 P Q N A B X D b
  c h)) (@finite_arrow_tail_rest (Functor_cat K C) (@OneCatNativeExactArrowPair K C (@additive_preadditive C
  Prod t Add) C1 t (@additive_terminal_object C Prod t Add) T0 P Q N) (succ (succ (succ zero)))
  (@kernel_adjunction_family_func K C (@additive_preadditive C Prod t Add) t (@additive_terminal_object C Prod t
  Add) P (@one_cat_native_snake_alpha_diagram K C (@additive_preadditive C Prod t Add) C1 t
  (@additive_terminal_object C Prod t Add) T0 P A B X D b c h)) (@kernel_adjunction_family_func K C
  (@additive_preadditive C Prod t Add) t (@additive_terminal_object C Prod t Add) P (@transf_arrow_diagram_func
  K C B X b)) (@one_cat_native_snake_kernel_first K C (@additive_preadditive C Prod t Add) C1 t
  (@additive_terminal_object C Prod t Add) T0 P Q A B X D b c h) (@one_cat_native_snake_six_term_result K C C1
  Prod t Add T0 P Q N A B X D b c h)))) (@finite_arrow_tail_arrow (Functor_cat K C) (@OneCatNativeExactArrowPair
  K C (@additive_preadditive C Prod t Add) C1 t (@additive_terminal_object C Prod t Add) T0 P Q N) (succ (succ
  zero)) (@kernel_adjunction_family_func K C (@additive_preadditive C Prod t Add) t (@additive_terminal_object C
  Prod t Add) P (@transf_arrow_diagram_func K C B X b)) (@finite_arrow_tail_next (Functor_cat K C)
  (@OneCatNativeExactArrowPair K C (@additive_preadditive C Prod t Add) C1 t (@additive_terminal_object C Prod t
  Add) T0 P Q N) (succ (succ (succ zero))) (@kernel_adjunction_family_func K C (@additive_preadditive C Prod t
  Add) t (@additive_terminal_object C Prod t Add) P (@one_cat_native_snake_alpha_diagram K C
  (@additive_preadditive C Prod t Add) C1 t (@additive_terminal_object C Prod t Add) T0 P A B X D b c h))
  (@kernel_adjunction_family_func K C (@additive_preadditive C Prod t Add) t (@additive_terminal_object C Prod t
  Add) P (@transf_arrow_diagram_func K C B X b)) (@one_cat_native_snake_kernel_first K C (@additive_preadditive
  C Prod t Add) C1 t (@additive_terminal_object C Prod t Add) T0 P Q A B X D b c h)
  (@one_cat_native_snake_six_term_result K C C1 Prod t Add T0 P Q N A B X D b c h)) (@finite_arrow_tail_arrow
  (Functor_cat K C) (@OneCatNativeExactArrowPair K C (@additive_preadditive C Prod t Add) C1 t
  (@additive_terminal_object C Prod t Add) T0 P Q N) (succ (succ (succ zero))) (@kernel_adjunction_family_func K
  C (@additive_preadditive C Prod t Add) t (@additive_terminal_object C Prod t Add) P
  (@one_cat_native_snake_alpha_diagram K C (@additive_preadditive C Prod t Add) C1 t (@additive_terminal_object
  C Prod t Add) T0 P A B X D b c h)) (@kernel_adjunction_family_func K C (@additive_preadditive C Prod t Add) t
  (@additive_terminal_object C Prod t Add) P (@transf_arrow_diagram_func K C B X b))
  (@one_cat_native_snake_kernel_first K C (@additive_preadditive C Prod t Add) C1 t (@additive_terminal_object C
  Prod t Add) T0 P Q A B X D b c h) (@one_cat_native_snake_six_term_result K C C1 Prod t Add T0 P Q N A B X D b
  c h)) (@finite_arrow_tail_rest (Functor_cat K C) (@OneCatNativeExactArrowPair K C (@additive_preadditive C
  Prod t Add) C1 t (@additive_terminal_object C Prod t Add) T0 P Q N) (succ (succ (succ zero)))
  (@kernel_adjunction_family_func K C (@additive_preadditive C Prod t Add) t (@additive_terminal_object C Prod t
  Add) P (@one_cat_native_snake_alpha_diagram K C (@additive_preadditive C Prod t Add) C1 t
  (@additive_terminal_object C Prod t Add) T0 P A B X D b c h)) (@kernel_adjunction_family_func K C
  (@additive_preadditive C Prod t Add) t (@additive_terminal_object C Prod t Add) P (@transf_arrow_diagram_func
  K C B X b)) (@one_cat_native_snake_kernel_first K C (@additive_preadditive C Prod t Add) C1 t
  (@additive_terminal_object C Prod t Add) T0 P Q A B X D b c h) (@one_cat_native_snake_six_term_result K C C1
  Prod t Add T0 P Q N A B X D b c h))) (@finite_arrow_tail_arrow (Functor_cat K C) (@OneCatNativeExactArrowPair
  K C (@additive_preadditive C Prod t Add) C1 t (@additive_terminal_object C Prod t Add) T0 P Q N) (succ zero)
  (@finite_arrow_tail_next (Functor_cat K C) (@OneCatNativeExactArrowPair K C (@additive_preadditive C Prod t
  Add) C1 t (@additive_terminal_object C Prod t Add) T0 P Q N) (succ (succ (succ zero)))
  (@kernel_adjunction_family_func K C (@additive_preadditive C Prod t Add) t (@additive_terminal_object C Prod t
  Add) P (@one_cat_native_snake_alpha_diagram K C (@additive_preadditive C Prod t Add) C1 t
  (@additive_terminal_object C Prod t Add) T0 P A B X D b c h)) (@kernel_adjunction_family_func K C
  (@additive_preadditive C Prod t Add) t (@additive_terminal_object C Prod t Add) P (@transf_arrow_diagram_func
  K C B X b)) (@one_cat_native_snake_kernel_first K C (@additive_preadditive C Prod t Add) C1 t
  (@additive_terminal_object C Prod t Add) T0 P Q A B X D b c h) (@one_cat_native_snake_six_term_result K C C1
  Prod t Add T0 P Q N A B X D b c h)) (@finite_arrow_tail_next (Functor_cat K C) (@OneCatNativeExactArrowPair K
  C (@additive_preadditive C Prod t Add) C1 t (@additive_terminal_object C Prod t Add) T0 P Q N) (succ (succ
  zero)) (@kernel_adjunction_family_func K C (@additive_preadditive C Prod t Add) t (@additive_terminal_object C
  Prod t Add) P (@transf_arrow_diagram_func K C B X b)) (@finite_arrow_tail_next (Functor_cat K C)
  (@OneCatNativeExactArrowPair K C (@additive_preadditive C Prod t Add) C1 t (@additive_terminal_object C Prod t
  Add) T0 P Q N) (succ (succ (succ zero))) (@kernel_adjunction_family_func K C (@additive_preadditive C Prod t
  Add) t (@additive_terminal_object C Prod t Add) P (@one_cat_native_snake_alpha_diagram K C
  (@additive_preadditive C Prod t Add) C1 t (@additive_terminal_object C Prod t Add) T0 P A B X D b c h))
  (@kernel_adjunction_family_func K C (@additive_preadditive C Prod t Add) t (@additive_terminal_object C Prod t
  Add) P (@transf_arrow_diagram_func K C B X b)) (@one_cat_native_snake_kernel_first K C (@additive_preadditive
  C Prod t Add) C1 t (@additive_terminal_object C Prod t Add) T0 P Q A B X D b c h)
  (@one_cat_native_snake_six_term_result K C C1 Prod t Add T0 P Q N A B X D b c h)) (@finite_arrow_tail_arrow
  (Functor_cat K C) (@OneCatNativeExactArrowPair K C (@additive_preadditive C Prod t Add) C1 t
  (@additive_terminal_object C Prod t Add) T0 P Q N) (succ (succ (succ zero))) (@kernel_adjunction_family_func K
  C (@additive_preadditive C Prod t Add) t (@additive_terminal_object C Prod t Add) P
  (@one_cat_native_snake_alpha_diagram K C (@additive_preadditive C Prod t Add) C1 t (@additive_terminal_object
  C Prod t Add) T0 P A B X D b c h)) (@kernel_adjunction_family_func K C (@additive_preadditive C Prod t Add) t
  (@additive_terminal_object C Prod t Add) P (@transf_arrow_diagram_func K C B X b))
  (@one_cat_native_snake_kernel_first K C (@additive_preadditive C Prod t Add) C1 t (@additive_terminal_object C
  Prod t Add) T0 P Q A B X D b c h) (@one_cat_native_snake_six_term_result K C C1 Prod t Add T0 P Q N A B X D b
  c h)) (@finite_arrow_tail_rest (Functor_cat K C) (@OneCatNativeExactArrowPair K C (@additive_preadditive C
  Prod t Add) C1 t (@additive_terminal_object C Prod t Add) T0 P Q N) (succ (succ (succ zero)))
  (@kernel_adjunction_family_func K C (@additive_preadditive C Prod t Add) t (@additive_terminal_object C Prod t
  Add) P (@one_cat_native_snake_alpha_diagram K C (@additive_preadditive C Prod t Add) C1 t
  (@additive_terminal_object C Prod t Add) T0 P A B X D b c h)) (@kernel_adjunction_family_func K C
  (@additive_preadditive C Prod t Add) t (@additive_terminal_object C Prod t Add) P (@transf_arrow_diagram_func
  K C B X b)) (@one_cat_native_snake_kernel_first K C (@additive_preadditive C Prod t Add) C1 t
  (@additive_terminal_object C Prod t Add) T0 P Q A B X D b c h) (@one_cat_native_snake_six_term_result K C C1
  Prod t Add T0 P Q N A B X D b c h))) (@finite_arrow_tail_arrow (Functor_cat K C) (@OneCatNativeExactArrowPair
  K C (@additive_preadditive C Prod t Add) C1 t (@additive_terminal_object C Prod t Add) T0 P Q N) (succ (succ
  zero)) (@kernel_adjunction_family_func K C (@additive_preadditive C Prod t Add) t (@additive_terminal_object C
  Prod t Add) P (@transf_arrow_diagram_func K C B X b)) (@finite_arrow_tail_next (Functor_cat K C)
  (@OneCatNativeExactArrowPair K C (@additive_preadditive C Prod t Add) C1 t (@additive_terminal_object C Prod t
  Add) T0 P Q N) (succ (succ (succ zero))) (@kernel_adjunction_family_func K C (@additive_preadditive C Prod t
  Add) t (@additive_terminal_object C Prod t Add) P (@one_cat_native_snake_alpha_diagram K C
  (@additive_preadditive C Prod t Add) C1 t (@additive_terminal_object C Prod t Add) T0 P A B X D b c h))
  (@kernel_adjunction_family_func K C (@additive_preadditive C Prod t Add) t (@additive_terminal_object C Prod t
  Add) P (@transf_arrow_diagram_func K C B X b)) (@one_cat_native_snake_kernel_first K C (@additive_preadditive
  C Prod t Add) C1 t (@additive_terminal_object C Prod t Add) T0 P Q A B X D b c h)
  (@one_cat_native_snake_six_term_result K C C1 Prod t Add T0 P Q N A B X D b c h)) (@finite_arrow_tail_arrow
  (Functor_cat K C) (@OneCatNativeExactArrowPair K C (@additive_preadditive C Prod t Add) C1 t
  (@additive_terminal_object C Prod t Add) T0 P Q N) (succ (succ (succ zero))) (@kernel_adjunction_family_func K
  C (@additive_preadditive C Prod t Add) t (@additive_terminal_object C Prod t Add) P
  (@one_cat_native_snake_alpha_diagram K C (@additive_preadditive C Prod t Add) C1 t (@additive_terminal_object
  C Prod t Add) T0 P A B X D b c h)) (@kernel_adjunction_family_func K C (@additive_preadditive C Prod t Add) t
  (@additive_terminal_object C Prod t Add) P (@transf_arrow_diagram_func K C B X b))
  (@one_cat_native_snake_kernel_first K C (@additive_preadditive C Prod t Add) C1 t (@additive_terminal_object C
  Prod t Add) T0 P Q A B X D b c h) (@one_cat_native_snake_six_term_result K C C1 Prod t Add T0 P Q N A B X D b
  c h)) (@finite_arrow_tail_rest (Functor_cat K C) (@OneCatNativeExactArrowPair K C (@additive_preadditive C
  Prod t Add) C1 t (@additive_terminal_object C Prod t Add) T0 P Q N) (succ (succ (succ zero)))
  (@kernel_adjunction_family_func K C (@additive_preadditive C Prod t Add) t (@additive_terminal_object C Prod t
  Add) P (@one_cat_native_snake_alpha_diagram K C (@additive_preadditive C Prod t Add) C1 t
  (@additive_terminal_object C Prod t Add) T0 P A B X D b c h)) (@kernel_adjunction_family_func K C
  (@additive_preadditive C Prod t Add) t (@additive_terminal_object C Prod t Add) P (@transf_arrow_diagram_func
  K C B X b)) (@one_cat_native_snake_kernel_first K C (@additive_preadditive C Prod t Add) C1 t
  (@additive_terminal_object C Prod t Add) T0 P Q A B X D b c h) (@one_cat_native_snake_six_term_result K C C1
  Prod t Add T0 P Q N A B X D b c h))) (@finite_arrow_tail_rest (Functor_cat K C) (@OneCatNativeExactArrowPair K
  C (@additive_preadditive C Prod t Add) C1 t (@additive_terminal_object C Prod t Add) T0 P Q N) (succ (succ
  zero)) (@kernel_adjunction_family_func K C (@additive_preadditive C Prod t Add) t (@additive_terminal_object C
  Prod t Add) P (@transf_arrow_diagram_func K C B X b)) (@finite_arrow_tail_next (Functor_cat K C)
  (@OneCatNativeExactArrowPair K C (@additive_preadditive C Prod t Add) C1 t (@additive_terminal_object C Prod t
  Add) T0 P Q N) (succ (succ (succ zero))) (@kernel_adjunction_family_func K C (@additive_preadditive C Prod t
  Add) t (@additive_terminal_object C Prod t Add) P (@one_cat_native_snake_alpha_diagram K C
  (@additive_preadditive C Prod t Add) C1 t (@additive_terminal_object C Prod t Add) T0 P A B X D b c h))
  (@kernel_adjunction_family_func K C (@additive_preadditive C Prod t Add) t (@additive_terminal_object C Prod t
  Add) P (@transf_arrow_diagram_func K C B X b)) (@one_cat_native_snake_kernel_first K C (@additive_preadditive
  C Prod t Add) C1 t (@additive_terminal_object C Prod t Add) T0 P Q A B X D b c h)
  (@one_cat_native_snake_six_term_result K C C1 Prod t Add T0 P Q N A B X D b c h)) (@finite_arrow_tail_arrow
  (Functor_cat K C) (@OneCatNativeExactArrowPair K C (@additive_preadditive C Prod t Add) C1 t
  (@additive_terminal_object C Prod t Add) T0 P Q N) (succ (succ (succ zero))) (@kernel_adjunction_family_func K
  C (@additive_preadditive C Prod t Add) t (@additive_terminal_object C Prod t Add) P
  (@one_cat_native_snake_alpha_diagram K C (@additive_preadditive C Prod t Add) C1 t (@additive_terminal_object
  C Prod t Add) T0 P A B X D b c h)) (@kernel_adjunction_family_func K C (@additive_preadditive C Prod t Add) t
  (@additive_terminal_object C Prod t Add) P (@transf_arrow_diagram_func K C B X b))
  (@one_cat_native_snake_kernel_first K C (@additive_preadditive C Prod t Add) C1 t (@additive_terminal_object C
  Prod t Add) T0 P Q A B X D b c h) (@one_cat_native_snake_six_term_result K C C1 Prod t Add T0 P Q N A B X D b
  c h)) (@finite_arrow_tail_rest (Functor_cat K C) (@OneCatNativeExactArrowPair K C (@additive_preadditive C
  Prod t Add) C1 t (@additive_terminal_object C Prod t Add) T0 P Q N) (succ (succ (succ zero)))
  (@kernel_adjunction_family_func K C (@additive_preadditive C Prod t Add) t (@additive_terminal_object C Prod t
  Add) P (@one_cat_native_snake_alpha_diagram K C (@additive_preadditive C Prod t Add) C1 t
  (@additive_terminal_object C Prod t Add) T0 P A B X D b c h)) (@kernel_adjunction_family_func K C
  (@additive_preadditive C Prod t Add) t (@additive_terminal_object C Prod t Add) P (@transf_arrow_diagram_func
  K C B X b)) (@one_cat_native_snake_kernel_first K C (@additive_preadditive C Prod t Add) C1 t
  (@additive_terminal_object C Prod t Add) T0 P Q A B X D b c h) (@one_cat_native_snake_six_term_result K C C1
  Prod t Add T0 P Q N A B X D b c h)))) (@finite_arrow_tail_step (Functor_cat K C) (@OneCatNativeExactArrowPair
  K C (@additive_preadditive C Prod t Add) C1 t (@additive_terminal_object C Prod t Add) T0 P Q N) (succ zero)
  (@finite_arrow_tail_next (Functor_cat K C) (@OneCatNativeExactArrowPair K C (@additive_preadditive C Prod t
  Add) C1 t (@additive_terminal_object C Prod t Add) T0 P Q N) (succ (succ (succ zero)))
  (@kernel_adjunction_family_func K C (@additive_preadditive C Prod t Add) t (@additive_terminal_object C Prod t
  Add) P (@one_cat_native_snake_alpha_diagram K C (@additive_preadditive C Prod t Add) C1 t
  (@additive_terminal_object C Prod t Add) T0 P A B X D b c h)) (@kernel_adjunction_family_func K C
  (@additive_preadditive C Prod t Add) t (@additive_terminal_object C Prod t Add) P (@transf_arrow_diagram_func
  K C B X b)) (@one_cat_native_snake_kernel_first K C (@additive_preadditive C Prod t Add) C1 t
  (@additive_terminal_object C Prod t Add) T0 P Q A B X D b c h) (@one_cat_native_snake_six_term_result K C C1
  Prod t Add T0 P Q N A B X D b c h)) (@finite_arrow_tail_next (Functor_cat K C) (@OneCatNativeExactArrowPair K
  C (@additive_preadditive C Prod t Add) C1 t (@additive_terminal_object C Prod t Add) T0 P Q N) (succ (succ
  zero)) (@kernel_adjunction_family_func K C (@additive_preadditive C Prod t Add) t (@additive_terminal_object C
  Prod t Add) P (@transf_arrow_diagram_func K C B X b)) (@finite_arrow_tail_next (Functor_cat K C)
  (@OneCatNativeExactArrowPair K C (@additive_preadditive C Prod t Add) C1 t (@additive_terminal_object C Prod t
  Add) T0 P Q N) (succ (succ (succ zero))) (@kernel_adjunction_family_func K C (@additive_preadditive C Prod t
  Add) t (@additive_terminal_object C Prod t Add) P (@one_cat_native_snake_alpha_diagram K C
  (@additive_preadditive C Prod t Add) C1 t (@additive_terminal_object C Prod t Add) T0 P A B X D b c h))
  (@kernel_adjunction_family_func K C (@additive_preadditive C Prod t Add) t (@additive_terminal_object C Prod t
  Add) P (@transf_arrow_diagram_func K C B X b)) (@one_cat_native_snake_kernel_first K C (@additive_preadditive
  C Prod t Add) C1 t (@additive_terminal_object C Prod t Add) T0 P Q A B X D b c h)
  (@one_cat_native_snake_six_term_result K C C1 Prod t Add T0 P Q N A B X D b c h)) (@finite_arrow_tail_arrow
  (Functor_cat K C) (@OneCatNativeExactArrowPair K C (@additive_preadditive C Prod t Add) C1 t
  (@additive_terminal_object C Prod t Add) T0 P Q N) (succ (succ (succ zero))) (@kernel_adjunction_family_func K
  C (@additive_preadditive C Prod t Add) t (@additive_terminal_object C Prod t Add) P
  (@one_cat_native_snake_alpha_diagram K C (@additive_preadditive C Prod t Add) C1 t (@additive_terminal_object
  C Prod t Add) T0 P A B X D b c h)) (@kernel_adjunction_family_func K C (@additive_preadditive C Prod t Add) t
  (@additive_terminal_object C Prod t Add) P (@transf_arrow_diagram_func K C B X b))
  (@one_cat_native_snake_kernel_first K C (@additive_preadditive C Prod t Add) C1 t (@additive_terminal_object C
  Prod t Add) T0 P Q A B X D b c h) (@one_cat_native_snake_six_term_result K C C1 Prod t Add T0 P Q N A B X D b
  c h)) (@finite_arrow_tail_rest (Functor_cat K C) (@OneCatNativeExactArrowPair K C (@additive_preadditive C
  Prod t Add) C1 t (@additive_terminal_object C Prod t Add) T0 P Q N) (succ (succ (succ zero)))
  (@kernel_adjunction_family_func K C (@additive_preadditive C Prod t Add) t (@additive_terminal_object C Prod t
  Add) P (@one_cat_native_snake_alpha_diagram K C (@additive_preadditive C Prod t Add) C1 t
  (@additive_terminal_object C Prod t Add) T0 P A B X D b c h)) (@kernel_adjunction_family_func K C
  (@additive_preadditive C Prod t Add) t (@additive_terminal_object C Prod t Add) P (@transf_arrow_diagram_func
  K C B X b)) (@one_cat_native_snake_kernel_first K C (@additive_preadditive C Prod t Add) C1 t
  (@additive_terminal_object C Prod t Add) T0 P Q A B X D b c h) (@one_cat_native_snake_six_term_result K C C1
  Prod t Add T0 P Q N A B X D b c h))) (@finite_arrow_tail_arrow (Functor_cat K C) (@OneCatNativeExactArrowPair
  K C (@additive_preadditive C Prod t Add) C1 t (@additive_terminal_object C Prod t Add) T0 P Q N) (succ (succ
  zero)) (@kernel_adjunction_family_func K C (@additive_preadditive C Prod t Add) t (@additive_terminal_object C
  Prod t Add) P (@transf_arrow_diagram_func K C B X b)) (@finite_arrow_tail_next (Functor_cat K C)
  (@OneCatNativeExactArrowPair K C (@additive_preadditive C Prod t Add) C1 t (@additive_terminal_object C Prod t
  Add) T0 P Q N) (succ (succ (succ zero))) (@kernel_adjunction_family_func K C (@additive_preadditive C Prod t
  Add) t (@additive_terminal_object C Prod t Add) P (@one_cat_native_snake_alpha_diagram K C
  (@additive_preadditive C Prod t Add) C1 t (@additive_terminal_object C Prod t Add) T0 P A B X D b c h))
  (@kernel_adjunction_family_func K C (@additive_preadditive C Prod t Add) t (@additive_terminal_object C Prod t
  Add) P (@transf_arrow_diagram_func K C B X b)) (@one_cat_native_snake_kernel_first K C (@additive_preadditive
  C Prod t Add) C1 t (@additive_terminal_object C Prod t Add) T0 P Q A B X D b c h)
  (@one_cat_native_snake_six_term_result K C C1 Prod t Add T0 P Q N A B X D b c h)) (@finite_arrow_tail_arrow
  (Functor_cat K C) (@OneCatNativeExactArrowPair K C (@additive_preadditive C Prod t Add) C1 t
  (@additive_terminal_object C Prod t Add) T0 P Q N) (succ (succ (succ zero))) (@kernel_adjunction_family_func K
  C (@additive_preadditive C Prod t Add) t (@additive_terminal_object C Prod t Add) P
  (@one_cat_native_snake_alpha_diagram K C (@additive_preadditive C Prod t Add) C1 t (@additive_terminal_object
  C Prod t Add) T0 P A B X D b c h)) (@kernel_adjunction_family_func K C (@additive_preadditive C Prod t Add) t
  (@additive_terminal_object C Prod t Add) P (@transf_arrow_diagram_func K C B X b))
  (@one_cat_native_snake_kernel_first K C (@additive_preadditive C Prod t Add) C1 t (@additive_terminal_object C
  Prod t Add) T0 P Q A B X D b c h) (@one_cat_native_snake_six_term_result K C C1 Prod t Add T0 P Q N A B X D b
  c h)) (@finite_arrow_tail_rest (Functor_cat K C) (@OneCatNativeExactArrowPair K C (@additive_preadditive C
  Prod t Add) C1 t (@additive_terminal_object C Prod t Add) T0 P Q N) (succ (succ (succ zero)))
  (@kernel_adjunction_family_func K C (@additive_preadditive C Prod t Add) t (@additive_terminal_object C Prod t
  Add) P (@one_cat_native_snake_alpha_diagram K C (@additive_preadditive C Prod t Add) C1 t
  (@additive_terminal_object C Prod t Add) T0 P A B X D b c h)) (@kernel_adjunction_family_func K C
  (@additive_preadditive C Prod t Add) t (@additive_terminal_object C Prod t Add) P (@transf_arrow_diagram_func
  K C B X b)) (@one_cat_native_snake_kernel_first K C (@additive_preadditive C Prod t Add) C1 t
  (@additive_terminal_object C Prod t Add) T0 P Q A B X D b c h) (@one_cat_native_snake_six_term_result K C C1
  Prod t Add T0 P Q N A B X D b c h))) (@finite_arrow_tail_rest (Functor_cat K C) (@OneCatNativeExactArrowPair K
  C (@additive_preadditive C Prod t Add) C1 t (@additive_terminal_object C Prod t Add) T0 P Q N) (succ (succ
  zero)) (@kernel_adjunction_family_func K C (@additive_preadditive C Prod t Add) t (@additive_terminal_object C
  Prod t Add) P (@transf_arrow_diagram_func K C B X b)) (@finite_arrow_tail_next (Functor_cat K C)
  (@OneCatNativeExactArrowPair K C (@additive_preadditive C Prod t Add) C1 t (@additive_terminal_object C Prod t
  Add) T0 P Q N) (succ (succ (succ zero))) (@kernel_adjunction_family_func K C (@additive_preadditive C Prod t
  Add) t (@additive_terminal_object C Prod t Add) P (@one_cat_native_snake_alpha_diagram K C
  (@additive_preadditive C Prod t Add) C1 t (@additive_terminal_object C Prod t Add) T0 P A B X D b c h))
  (@kernel_adjunction_family_func K C (@additive_preadditive C Prod t Add) t (@additive_terminal_object C Prod t
  Add) P (@transf_arrow_diagram_func K C B X b)) (@one_cat_native_snake_kernel_first K C (@additive_preadditive
  C Prod t Add) C1 t (@additive_terminal_object C Prod t Add) T0 P Q A B X D b c h)
  (@one_cat_native_snake_six_term_result K C C1 Prod t Add T0 P Q N A B X D b c h)) (@finite_arrow_tail_arrow
  (Functor_cat K C) (@OneCatNativeExactArrowPair K C (@additive_preadditive C Prod t Add) C1 t
  (@additive_terminal_object C Prod t Add) T0 P Q N) (succ (succ (succ zero))) (@kernel_adjunction_family_func K
  C (@additive_preadditive C Prod t Add) t (@additive_terminal_object C Prod t Add) P
  (@one_cat_native_snake_alpha_diagram K C (@additive_preadditive C Prod t Add) C1 t (@additive_terminal_object
  C Prod t Add) T0 P A B X D b c h)) (@kernel_adjunction_family_func K C (@additive_preadditive C Prod t Add) t
  (@additive_terminal_object C Prod t Add) P (@transf_arrow_diagram_func K C B X b))
  (@one_cat_native_snake_kernel_first K C (@additive_preadditive C Prod t Add) C1 t (@additive_terminal_object C
  Prod t Add) T0 P Q A B X D b c h) (@one_cat_native_snake_six_term_result K C C1 Prod t Add T0 P Q N A B X D b
  c h)) (@finite_arrow_tail_rest (Functor_cat K C) (@OneCatNativeExactArrowPair K C (@additive_preadditive C
  Prod t Add) C1 t (@additive_terminal_object C Prod t Add) T0 P Q N) (succ (succ (succ zero)))
  (@kernel_adjunction_family_func K C (@additive_preadditive C Prod t Add) t (@additive_terminal_object C Prod t
  Add) P (@one_cat_native_snake_alpha_diagram K C (@additive_preadditive C Prod t Add) C1 t
  (@additive_terminal_object C Prod t Add) T0 P A B X D b c h)) (@kernel_adjunction_family_func K C
  (@additive_preadditive C Prod t Add) t (@additive_terminal_object C Prod t Add) P (@transf_arrow_diagram_func
  K C B X b)) (@one_cat_native_snake_kernel_first K C (@additive_preadditive C Prod t Add) C1 t
  (@additive_terminal_object C Prod t Add) T0 P Q A B X D b c h) (@one_cat_native_snake_six_term_result K C C1
  Prod t Add T0 P Q N A B X D b c h)))))
  : τ (@= (@Transf K C (@finite_arrow_tail_next (Functor_cat K C) (@OneCatNativeExactArrowPair K C
  (@additive_preadditive C Prod t Add) C1 t (@additive_terminal_object C Prod t Add) T0 P Q N) (succ (succ (succ
  zero))) (@kernel_adjunction_family_func K C (@additive_preadditive C Prod t Add) t (@additive_terminal_object
  C Prod t Add) P (@one_cat_native_snake_alpha_diagram K C (@additive_preadditive C Prod t Add) C1 t
  (@additive_terminal_object C Prod t Add) T0 P A B X D b c h)) (@kernel_adjunction_family_func K C
  (@additive_preadditive C Prod t Add) t (@additive_terminal_object C Prod t Add) P (@transf_arrow_diagram_func
  K C B X b)) (@one_cat_native_snake_kernel_first K C (@additive_preadditive C Prod t Add) C1 t
  (@additive_terminal_object C Prod t Add) T0 P Q A B X D b c h) (@one_cat_native_snake_six_term_result K C C1
  Prod t Add T0 P Q N A B X D b c h)) (@finite_arrow_tail_next (Functor_cat K C) (@OneCatNativeExactArrowPair K
  C (@additive_preadditive C Prod t Add) C1 t (@additive_terminal_object C Prod t Add) T0 P Q N) (succ zero)
  (@finite_arrow_tail_next (Functor_cat K C) (@OneCatNativeExactArrowPair K C (@additive_preadditive C Prod t
  Add) C1 t (@additive_terminal_object C Prod t Add) T0 P Q N) (succ (succ (succ zero)))
  (@kernel_adjunction_family_func K C (@additive_preadditive C Prod t Add) t (@additive_terminal_object C Prod t
  Add) P (@one_cat_native_snake_alpha_diagram K C (@additive_preadditive C Prod t Add) C1 t
  (@additive_terminal_object C Prod t Add) T0 P A B X D b c h)) (@kernel_adjunction_family_func K C
  (@additive_preadditive C Prod t Add) t (@additive_terminal_object C Prod t Add) P (@transf_arrow_diagram_func
  K C B X b)) (@one_cat_native_snake_kernel_first K C (@additive_preadditive C Prod t Add) C1 t
  (@additive_terminal_object C Prod t Add) T0 P Q A B X D b c h) (@one_cat_native_snake_six_term_result K C C1
  Prod t Add T0 P Q N A B X D b c h)) (@finite_arrow_tail_next (Functor_cat K C) (@OneCatNativeExactArrowPair K
  C (@additive_preadditive C Prod t Add) C1 t (@additive_terminal_object C Prod t Add) T0 P Q N) (succ (succ
  zero)) (@kernel_adjunction_family_func K C (@additive_preadditive C Prod t Add) t (@additive_terminal_object C
  Prod t Add) P (@transf_arrow_diagram_func K C B X b)) (@finite_arrow_tail_next (Functor_cat K C)
  (@OneCatNativeExactArrowPair K C (@additive_preadditive C Prod t Add) C1 t (@additive_terminal_object C Prod t
  Add) T0 P Q N) (succ (succ (succ zero))) (@kernel_adjunction_family_func K C (@additive_preadditive C Prod t
  Add) t (@additive_terminal_object C Prod t Add) P (@one_cat_native_snake_alpha_diagram K C
  (@additive_preadditive C Prod t Add) C1 t (@additive_terminal_object C Prod t Add) T0 P A B X D b c h))
  (@kernel_adjunction_family_func K C (@additive_preadditive C Prod t Add) t (@additive_terminal_object C Prod t
  Add) P (@transf_arrow_diagram_func K C B X b)) (@one_cat_native_snake_kernel_first K C (@additive_preadditive
  C Prod t Add) C1 t (@additive_terminal_object C Prod t Add) T0 P Q A B X D b c h)
  (@one_cat_native_snake_six_term_result K C C1 Prod t Add T0 P Q N A B X D b c h)) (@finite_arrow_tail_arrow
  (Functor_cat K C) (@OneCatNativeExactArrowPair K C (@additive_preadditive C Prod t Add) C1 t
  (@additive_terminal_object C Prod t Add) T0 P Q N) (succ (succ (succ zero))) (@kernel_adjunction_family_func K
  C (@additive_preadditive C Prod t Add) t (@additive_terminal_object C Prod t Add) P
  (@one_cat_native_snake_alpha_diagram K C (@additive_preadditive C Prod t Add) C1 t (@additive_terminal_object
  C Prod t Add) T0 P A B X D b c h)) (@kernel_adjunction_family_func K C (@additive_preadditive C Prod t Add) t
  (@additive_terminal_object C Prod t Add) P (@transf_arrow_diagram_func K C B X b))
  (@one_cat_native_snake_kernel_first K C (@additive_preadditive C Prod t Add) C1 t (@additive_terminal_object C
  Prod t Add) T0 P Q A B X D b c h) (@one_cat_native_snake_six_term_result K C C1 Prod t Add T0 P Q N A B X D b
  c h)) (@finite_arrow_tail_rest (Functor_cat K C) (@OneCatNativeExactArrowPair K C (@additive_preadditive C
  Prod t Add) C1 t (@additive_terminal_object C Prod t Add) T0 P Q N) (succ (succ (succ zero)))
  (@kernel_adjunction_family_func K C (@additive_preadditive C Prod t Add) t (@additive_terminal_object C Prod t
  Add) P (@one_cat_native_snake_alpha_diagram K C (@additive_preadditive C Prod t Add) C1 t
  (@additive_terminal_object C Prod t Add) T0 P A B X D b c h)) (@kernel_adjunction_family_func K C
  (@additive_preadditive C Prod t Add) t (@additive_terminal_object C Prod t Add) P (@transf_arrow_diagram_func
  K C B X b)) (@one_cat_native_snake_kernel_first K C (@additive_preadditive C Prod t Add) C1 t
  (@additive_terminal_object C Prod t Add) T0 P Q A B X D b c h) (@one_cat_native_snake_six_term_result K C C1
  Prod t Add T0 P Q N A B X D b c h))) (@finite_arrow_tail_arrow (Functor_cat K C) (@OneCatNativeExactArrowPair
  K C (@additive_preadditive C Prod t Add) C1 t (@additive_terminal_object C Prod t Add) T0 P Q N) (succ (succ
  zero)) (@kernel_adjunction_family_func K C (@additive_preadditive C Prod t Add) t (@additive_terminal_object C
  Prod t Add) P (@transf_arrow_diagram_func K C B X b)) (@finite_arrow_tail_next (Functor_cat K C)
  (@OneCatNativeExactArrowPair K C (@additive_preadditive C Prod t Add) C1 t (@additive_terminal_object C Prod t
  Add) T0 P Q N) (succ (succ (succ zero))) (@kernel_adjunction_family_func K C (@additive_preadditive C Prod t
  Add) t (@additive_terminal_object C Prod t Add) P (@one_cat_native_snake_alpha_diagram K C
  (@additive_preadditive C Prod t Add) C1 t (@additive_terminal_object C Prod t Add) T0 P A B X D b c h))
  (@kernel_adjunction_family_func K C (@additive_preadditive C Prod t Add) t (@additive_terminal_object C Prod t
  Add) P (@transf_arrow_diagram_func K C B X b)) (@one_cat_native_snake_kernel_first K C (@additive_preadditive
  C Prod t Add) C1 t (@additive_terminal_object C Prod t Add) T0 P Q A B X D b c h)
  (@one_cat_native_snake_six_term_result K C C1 Prod t Add T0 P Q N A B X D b c h)) (@finite_arrow_tail_arrow
  (Functor_cat K C) (@OneCatNativeExactArrowPair K C (@additive_preadditive C Prod t Add) C1 t
  (@additive_terminal_object C Prod t Add) T0 P Q N) (succ (succ (succ zero))) (@kernel_adjunction_family_func K
  C (@additive_preadditive C Prod t Add) t (@additive_terminal_object C Prod t Add) P
  (@one_cat_native_snake_alpha_diagram K C (@additive_preadditive C Prod t Add) C1 t (@additive_terminal_object
  C Prod t Add) T0 P A B X D b c h)) (@kernel_adjunction_family_func K C (@additive_preadditive C Prod t Add) t
  (@additive_terminal_object C Prod t Add) P (@transf_arrow_diagram_func K C B X b))
  (@one_cat_native_snake_kernel_first K C (@additive_preadditive C Prod t Add) C1 t (@additive_terminal_object C
  Prod t Add) T0 P Q A B X D b c h) (@one_cat_native_snake_six_term_result K C C1 Prod t Add T0 P Q N A B X D b
  c h)) (@finite_arrow_tail_rest (Functor_cat K C) (@OneCatNativeExactArrowPair K C (@additive_preadditive C
  Prod t Add) C1 t (@additive_terminal_object C Prod t Add) T0 P Q N) (succ (succ (succ zero)))
  (@kernel_adjunction_family_func K C (@additive_preadditive C Prod t Add) t (@additive_terminal_object C Prod t
  Add) P (@one_cat_native_snake_alpha_diagram K C (@additive_preadditive C Prod t Add) C1 t
  (@additive_terminal_object C Prod t Add) T0 P A B X D b c h)) (@kernel_adjunction_family_func K C
  (@additive_preadditive C Prod t Add) t (@additive_terminal_object C Prod t Add) P (@transf_arrow_diagram_func
  K C B X b)) (@one_cat_native_snake_kernel_first K C (@additive_preadditive C Prod t Add) C1 t
  (@additive_terminal_object C Prod t Add) T0 P Q A B X D b c h) (@one_cat_native_snake_six_term_result K C C1
  Prod t Add T0 P Q N A B X D b c h))) (@finite_arrow_tail_rest (Functor_cat K C) (@OneCatNativeExactArrowPair K
  C (@additive_preadditive C Prod t Add) C1 t (@additive_terminal_object C Prod t Add) T0 P Q N) (succ (succ
  zero)) (@kernel_adjunction_family_func K C (@additive_preadditive C Prod t Add) t (@additive_terminal_object C
  Prod t Add) P (@transf_arrow_diagram_func K C B X b)) (@finite_arrow_tail_next (Functor_cat K C)
  (@OneCatNativeExactArrowPair K C (@additive_preadditive C Prod t Add) C1 t (@additive_terminal_object C Prod t
  Add) T0 P Q N) (succ (succ (succ zero))) (@kernel_adjunction_family_func K C (@additive_preadditive C Prod t
  Add) t (@additive_terminal_object C Prod t Add) P (@one_cat_native_snake_alpha_diagram K C
  (@additive_preadditive C Prod t Add) C1 t (@additive_terminal_object C Prod t Add) T0 P A B X D b c h))
  (@kernel_adjunction_family_func K C (@additive_preadditive C Prod t Add) t (@additive_terminal_object C Prod t
  Add) P (@transf_arrow_diagram_func K C B X b)) (@one_cat_native_snake_kernel_first K C (@additive_preadditive
  C Prod t Add) C1 t (@additive_terminal_object C Prod t Add) T0 P Q A B X D b c h)
  (@one_cat_native_snake_six_term_result K C C1 Prod t Add T0 P Q N A B X D b c h)) (@finite_arrow_tail_arrow
  (Functor_cat K C) (@OneCatNativeExactArrowPair K C (@additive_preadditive C Prod t Add) C1 t
  (@additive_terminal_object C Prod t Add) T0 P Q N) (succ (succ (succ zero))) (@kernel_adjunction_family_func K
  C (@additive_preadditive C Prod t Add) t (@additive_terminal_object C Prod t Add) P
  (@one_cat_native_snake_alpha_diagram K C (@additive_preadditive C Prod t Add) C1 t (@additive_terminal_object
  C Prod t Add) T0 P A B X D b c h)) (@kernel_adjunction_family_func K C (@additive_preadditive C Prod t Add) t
  (@additive_terminal_object C Prod t Add) P (@transf_arrow_diagram_func K C B X b))
  (@one_cat_native_snake_kernel_first K C (@additive_preadditive C Prod t Add) C1 t (@additive_terminal_object C
  Prod t Add) T0 P Q A B X D b c h) (@one_cat_native_snake_six_term_result K C C1 Prod t Add T0 P Q N A B X D b
  c h)) (@finite_arrow_tail_rest (Functor_cat K C) (@OneCatNativeExactArrowPair K C (@additive_preadditive C
  Prod t Add) C1 t (@additive_terminal_object C Prod t Add) T0 P Q N) (succ (succ (succ zero)))
  (@kernel_adjunction_family_func K C (@additive_preadditive C Prod t Add) t (@additive_terminal_object C Prod t
  Add) P (@one_cat_native_snake_alpha_diagram K C (@additive_preadditive C Prod t Add) C1 t
  (@additive_terminal_object C Prod t Add) T0 P A B X D b c h)) (@kernel_adjunction_family_func K C
  (@additive_preadditive C Prod t Add) t (@additive_terminal_object C Prod t Add) P (@transf_arrow_diagram_func
  K C B X b)) (@one_cat_native_snake_kernel_first K C (@additive_preadditive C Prod t Add) C1 t
  (@additive_terminal_object C Prod t Add) T0 P Q A B X D b c h) (@one_cat_native_snake_six_term_result K C C1
  Prod t Add T0 P Q N A B X D b c h))))) (@comp_fapp0 (Functor_cat K C) (@finite_arrow_tail_next (Functor_cat K
  C) (@OneCatNativeExactArrowPair K C (@additive_preadditive C Prod t Add) C1 t (@additive_terminal_object C
  Prod t Add) T0 P Q N) (succ (succ (succ zero))) (@kernel_adjunction_family_func K C (@additive_preadditive C
  Prod t Add) t (@additive_terminal_object C Prod t Add) P (@one_cat_native_snake_alpha_diagram K C
  (@additive_preadditive C Prod t Add) C1 t (@additive_terminal_object C Prod t Add) T0 P A B X D b c h))
  (@kernel_adjunction_family_func K C (@additive_preadditive C Prod t Add) t (@additive_terminal_object C Prod t
  Add) P (@transf_arrow_diagram_func K C B X b)) (@one_cat_native_snake_kernel_first K C (@additive_preadditive
  C Prod t Add) C1 t (@additive_terminal_object C Prod t Add) T0 P Q A B X D b c h)
  (@one_cat_native_snake_six_term_result K C C1 Prod t Add T0 P Q N A B X D b c h)) (@finite_arrow_tail_next
  (Functor_cat K C) (@OneCatNativeExactArrowPair K C (@additive_preadditive C Prod t Add) C1 t
  (@additive_terminal_object C Prod t Add) T0 P Q N) (succ (succ zero)) (@kernel_adjunction_family_func K C
  (@additive_preadditive C Prod t Add) t (@additive_terminal_object C Prod t Add) P (@transf_arrow_diagram_func
  K C B X b)) (@finite_arrow_tail_next (Functor_cat K C) (@OneCatNativeExactArrowPair K C (@additive_preadditive
  C Prod t Add) C1 t (@additive_terminal_object C Prod t Add) T0 P Q N) (succ (succ (succ zero)))
  (@kernel_adjunction_family_func K C (@additive_preadditive C Prod t Add) t (@additive_terminal_object C Prod t
  Add) P (@one_cat_native_snake_alpha_diagram K C (@additive_preadditive C Prod t Add) C1 t
  (@additive_terminal_object C Prod t Add) T0 P A B X D b c h)) (@kernel_adjunction_family_func K C
  (@additive_preadditive C Prod t Add) t (@additive_terminal_object C Prod t Add) P (@transf_arrow_diagram_func
  K C B X b)) (@one_cat_native_snake_kernel_first K C (@additive_preadditive C Prod t Add) C1 t
  (@additive_terminal_object C Prod t Add) T0 P Q A B X D b c h) (@one_cat_native_snake_six_term_result K C C1
  Prod t Add T0 P Q N A B X D b c h)) (@finite_arrow_tail_arrow (Functor_cat K C) (@OneCatNativeExactArrowPair K
  C (@additive_preadditive C Prod t Add) C1 t (@additive_terminal_object C Prod t Add) T0 P Q N) (succ (succ
  (succ zero))) (@kernel_adjunction_family_func K C (@additive_preadditive C Prod t Add) t
  (@additive_terminal_object C Prod t Add) P (@one_cat_native_snake_alpha_diagram K C (@additive_preadditive C
  Prod t Add) C1 t (@additive_terminal_object C Prod t Add) T0 P A B X D b c h)) (@kernel_adjunction_family_func
  K C (@additive_preadditive C Prod t Add) t (@additive_terminal_object C Prod t Add) P
  (@transf_arrow_diagram_func K C B X b)) (@one_cat_native_snake_kernel_first K C (@additive_preadditive C Prod
  t Add) C1 t (@additive_terminal_object C Prod t Add) T0 P Q A B X D b c h)
  (@one_cat_native_snake_six_term_result K C C1 Prod t Add T0 P Q N A B X D b c h)) (@finite_arrow_tail_rest
  (Functor_cat K C) (@OneCatNativeExactArrowPair K C (@additive_preadditive C Prod t Add) C1 t
  (@additive_terminal_object C Prod t Add) T0 P Q N) (succ (succ (succ zero))) (@kernel_adjunction_family_func K
  C (@additive_preadditive C Prod t Add) t (@additive_terminal_object C Prod t Add) P
  (@one_cat_native_snake_alpha_diagram K C (@additive_preadditive C Prod t Add) C1 t (@additive_terminal_object
  C Prod t Add) T0 P A B X D b c h)) (@kernel_adjunction_family_func K C (@additive_preadditive C Prod t Add) t
  (@additive_terminal_object C Prod t Add) P (@transf_arrow_diagram_func K C B X b))
  (@one_cat_native_snake_kernel_first K C (@additive_preadditive C Prod t Add) C1 t (@additive_terminal_object C
  Prod t Add) T0 P Q A B X D b c h) (@one_cat_native_snake_six_term_result K C C1 Prod t Add T0 P Q N A B X D b
  c h))) (@finite_arrow_tail_next (Functor_cat K C) (@OneCatNativeExactArrowPair K C (@additive_preadditive C
  Prod t Add) C1 t (@additive_terminal_object C Prod t Add) T0 P Q N) (succ zero) (@finite_arrow_tail_next
  (Functor_cat K C) (@OneCatNativeExactArrowPair K C (@additive_preadditive C Prod t Add) C1 t
  (@additive_terminal_object C Prod t Add) T0 P Q N) (succ (succ (succ zero))) (@kernel_adjunction_family_func K
  C (@additive_preadditive C Prod t Add) t (@additive_terminal_object C Prod t Add) P
  (@one_cat_native_snake_alpha_diagram K C (@additive_preadditive C Prod t Add) C1 t (@additive_terminal_object
  C Prod t Add) T0 P A B X D b c h)) (@kernel_adjunction_family_func K C (@additive_preadditive C Prod t Add) t
  (@additive_terminal_object C Prod t Add) P (@transf_arrow_diagram_func K C B X b))
  (@one_cat_native_snake_kernel_first K C (@additive_preadditive C Prod t Add) C1 t (@additive_terminal_object C
  Prod t Add) T0 P Q A B X D b c h) (@one_cat_native_snake_six_term_result K C C1 Prod t Add T0 P Q N A B X D b
  c h)) (@finite_arrow_tail_next (Functor_cat K C) (@OneCatNativeExactArrowPair K C (@additive_preadditive C
  Prod t Add) C1 t (@additive_terminal_object C Prod t Add) T0 P Q N) (succ (succ zero))
  (@kernel_adjunction_family_func K C (@additive_preadditive C Prod t Add) t (@additive_terminal_object C Prod t
  Add) P (@transf_arrow_diagram_func K C B X b)) (@finite_arrow_tail_next (Functor_cat K C)
  (@OneCatNativeExactArrowPair K C (@additive_preadditive C Prod t Add) C1 t (@additive_terminal_object C Prod t
  Add) T0 P Q N) (succ (succ (succ zero))) (@kernel_adjunction_family_func K C (@additive_preadditive C Prod t
  Add) t (@additive_terminal_object C Prod t Add) P (@one_cat_native_snake_alpha_diagram K C
  (@additive_preadditive C Prod t Add) C1 t (@additive_terminal_object C Prod t Add) T0 P A B X D b c h))
  (@kernel_adjunction_family_func K C (@additive_preadditive C Prod t Add) t (@additive_terminal_object C Prod t
  Add) P (@transf_arrow_diagram_func K C B X b)) (@one_cat_native_snake_kernel_first K C (@additive_preadditive
  C Prod t Add) C1 t (@additive_terminal_object C Prod t Add) T0 P Q A B X D b c h)
  (@one_cat_native_snake_six_term_result K C C1 Prod t Add T0 P Q N A B X D b c h)) (@finite_arrow_tail_arrow
  (Functor_cat K C) (@OneCatNativeExactArrowPair K C (@additive_preadditive C Prod t Add) C1 t
  (@additive_terminal_object C Prod t Add) T0 P Q N) (succ (succ (succ zero))) (@kernel_adjunction_family_func K
  C (@additive_preadditive C Prod t Add) t (@additive_terminal_object C Prod t Add) P
  (@one_cat_native_snake_alpha_diagram K C (@additive_preadditive C Prod t Add) C1 t (@additive_terminal_object
  C Prod t Add) T0 P A B X D b c h)) (@kernel_adjunction_family_func K C (@additive_preadditive C Prod t Add) t
  (@additive_terminal_object C Prod t Add) P (@transf_arrow_diagram_func K C B X b))
  (@one_cat_native_snake_kernel_first K C (@additive_preadditive C Prod t Add) C1 t (@additive_terminal_object C
  Prod t Add) T0 P Q A B X D b c h) (@one_cat_native_snake_six_term_result K C C1 Prod t Add T0 P Q N A B X D b
  c h)) (@finite_arrow_tail_rest (Functor_cat K C) (@OneCatNativeExactArrowPair K C (@additive_preadditive C
  Prod t Add) C1 t (@additive_terminal_object C Prod t Add) T0 P Q N) (succ (succ (succ zero)))
  (@kernel_adjunction_family_func K C (@additive_preadditive C Prod t Add) t (@additive_terminal_object C Prod t
  Add) P (@one_cat_native_snake_alpha_diagram K C (@additive_preadditive C Prod t Add) C1 t
  (@additive_terminal_object C Prod t Add) T0 P A B X D b c h)) (@kernel_adjunction_family_func K C
  (@additive_preadditive C Prod t Add) t (@additive_terminal_object C Prod t Add) P (@transf_arrow_diagram_func
  K C B X b)) (@one_cat_native_snake_kernel_first K C (@additive_preadditive C Prod t Add) C1 t
  (@additive_terminal_object C Prod t Add) T0 P Q A B X D b c h) (@one_cat_native_snake_six_term_result K C C1
  Prod t Add T0 P Q N A B X D b c h))) (@finite_arrow_tail_arrow (Functor_cat K C) (@OneCatNativeExactArrowPair
  K C (@additive_preadditive C Prod t Add) C1 t (@additive_terminal_object C Prod t Add) T0 P Q N) (succ (succ
  zero)) (@kernel_adjunction_family_func K C (@additive_preadditive C Prod t Add) t (@additive_terminal_object C
  Prod t Add) P (@transf_arrow_diagram_func K C B X b)) (@finite_arrow_tail_next (Functor_cat K C)
  (@OneCatNativeExactArrowPair K C (@additive_preadditive C Prod t Add) C1 t (@additive_terminal_object C Prod t
  Add) T0 P Q N) (succ (succ (succ zero))) (@kernel_adjunction_family_func K C (@additive_preadditive C Prod t
  Add) t (@additive_terminal_object C Prod t Add) P (@one_cat_native_snake_alpha_diagram K C
  (@additive_preadditive C Prod t Add) C1 t (@additive_terminal_object C Prod t Add) T0 P A B X D b c h))
  (@kernel_adjunction_family_func K C (@additive_preadditive C Prod t Add) t (@additive_terminal_object C Prod t
  Add) P (@transf_arrow_diagram_func K C B X b)) (@one_cat_native_snake_kernel_first K C (@additive_preadditive
  C Prod t Add) C1 t (@additive_terminal_object C Prod t Add) T0 P Q A B X D b c h)
  (@one_cat_native_snake_six_term_result K C C1 Prod t Add T0 P Q N A B X D b c h)) (@finite_arrow_tail_arrow
  (Functor_cat K C) (@OneCatNativeExactArrowPair K C (@additive_preadditive C Prod t Add) C1 t
  (@additive_terminal_object C Prod t Add) T0 P Q N) (succ (succ (succ zero))) (@kernel_adjunction_family_func K
  C (@additive_preadditive C Prod t Add) t (@additive_terminal_object C Prod t Add) P
  (@one_cat_native_snake_alpha_diagram K C (@additive_preadditive C Prod t Add) C1 t (@additive_terminal_object
  C Prod t Add) T0 P A B X D b c h)) (@kernel_adjunction_family_func K C (@additive_preadditive C Prod t Add) t
  (@additive_terminal_object C Prod t Add) P (@transf_arrow_diagram_func K C B X b))
  (@one_cat_native_snake_kernel_first K C (@additive_preadditive C Prod t Add) C1 t (@additive_terminal_object C
  Prod t Add) T0 P Q A B X D b c h) (@one_cat_native_snake_six_term_result K C C1 Prod t Add T0 P Q N A B X D b
  c h)) (@finite_arrow_tail_rest (Functor_cat K C) (@OneCatNativeExactArrowPair K C (@additive_preadditive C
  Prod t Add) C1 t (@additive_terminal_object C Prod t Add) T0 P Q N) (succ (succ (succ zero)))
  (@kernel_adjunction_family_func K C (@additive_preadditive C Prod t Add) t (@additive_terminal_object C Prod t
  Add) P (@one_cat_native_snake_alpha_diagram K C (@additive_preadditive C Prod t Add) C1 t
  (@additive_terminal_object C Prod t Add) T0 P A B X D b c h)) (@kernel_adjunction_family_func K C
  (@additive_preadditive C Prod t Add) t (@additive_terminal_object C Prod t Add) P (@transf_arrow_diagram_func
  K C B X b)) (@one_cat_native_snake_kernel_first K C (@additive_preadditive C Prod t Add) C1 t
  (@additive_terminal_object C Prod t Add) T0 P Q A B X D b c h) (@one_cat_native_snake_six_term_result K C C1
  Prod t Add T0 P Q N A B X D b c h))) (@finite_arrow_tail_rest (Functor_cat K C) (@OneCatNativeExactArrowPair K
  C (@additive_preadditive C Prod t Add) C1 t (@additive_terminal_object C Prod t Add) T0 P Q N) (succ (succ
  zero)) (@kernel_adjunction_family_func K C (@additive_preadditive C Prod t Add) t (@additive_terminal_object C
  Prod t Add) P (@transf_arrow_diagram_func K C B X b)) (@finite_arrow_tail_next (Functor_cat K C)
  (@OneCatNativeExactArrowPair K C (@additive_preadditive C Prod t Add) C1 t (@additive_terminal_object C Prod t
  Add) T0 P Q N) (succ (succ (succ zero))) (@kernel_adjunction_family_func K C (@additive_preadditive C Prod t
  Add) t (@additive_terminal_object C Prod t Add) P (@one_cat_native_snake_alpha_diagram K C
  (@additive_preadditive C Prod t Add) C1 t (@additive_terminal_object C Prod t Add) T0 P A B X D b c h))
  (@kernel_adjunction_family_func K C (@additive_preadditive C Prod t Add) t (@additive_terminal_object C Prod t
  Add) P (@transf_arrow_diagram_func K C B X b)) (@one_cat_native_snake_kernel_first K C (@additive_preadditive
  C Prod t Add) C1 t (@additive_terminal_object C Prod t Add) T0 P Q A B X D b c h)
  (@one_cat_native_snake_six_term_result K C C1 Prod t Add T0 P Q N A B X D b c h)) (@finite_arrow_tail_arrow
  (Functor_cat K C) (@OneCatNativeExactArrowPair K C (@additive_preadditive C Prod t Add) C1 t
  (@additive_terminal_object C Prod t Add) T0 P Q N) (succ (succ (succ zero))) (@kernel_adjunction_family_func K
  C (@additive_preadditive C Prod t Add) t (@additive_terminal_object C Prod t Add) P
  (@one_cat_native_snake_alpha_diagram K C (@additive_preadditive C Prod t Add) C1 t (@additive_terminal_object
  C Prod t Add) T0 P A B X D b c h)) (@kernel_adjunction_family_func K C (@additive_preadditive C Prod t Add) t
  (@additive_terminal_object C Prod t Add) P (@transf_arrow_diagram_func K C B X b))
  (@one_cat_native_snake_kernel_first K C (@additive_preadditive C Prod t Add) C1 t (@additive_terminal_object C
  Prod t Add) T0 P Q A B X D b c h) (@one_cat_native_snake_six_term_result K C C1 Prod t Add T0 P Q N A B X D b
  c h)) (@finite_arrow_tail_rest (Functor_cat K C) (@OneCatNativeExactArrowPair K C (@additive_preadditive C
  Prod t Add) C1 t (@additive_terminal_object C Prod t Add) T0 P Q N) (succ (succ (succ zero)))
  (@kernel_adjunction_family_func K C (@additive_preadditive C Prod t Add) t (@additive_terminal_object C Prod t
  Add) P (@one_cat_native_snake_alpha_diagram K C (@additive_preadditive C Prod t Add) C1 t
  (@additive_terminal_object C Prod t Add) T0 P A B X D b c h)) (@kernel_adjunction_family_func K C
  (@additive_preadditive C Prod t Add) t (@additive_terminal_object C Prod t Add) P (@transf_arrow_diagram_func
  K C B X b)) (@one_cat_native_snake_kernel_first K C (@additive_preadditive C Prod t Add) C1 t
  (@additive_terminal_object C Prod t Add) T0 P Q A B X D b c h) (@one_cat_native_snake_six_term_result K C C1
  Prod t Add T0 P Q N A B X D b c h)))) (@finite_arrow_tail_arrow (Functor_cat K C) (@OneCatNativeExactArrowPair
  K C (@additive_preadditive C Prod t Add) C1 t (@additive_terminal_object C Prod t Add) T0 P Q N) (succ zero)
  (@finite_arrow_tail_next (Functor_cat K C) (@OneCatNativeExactArrowPair K C (@additive_preadditive C Prod t
  Add) C1 t (@additive_terminal_object C Prod t Add) T0 P Q N) (succ (succ (succ zero)))
  (@kernel_adjunction_family_func K C (@additive_preadditive C Prod t Add) t (@additive_terminal_object C Prod t
  Add) P (@one_cat_native_snake_alpha_diagram K C (@additive_preadditive C Prod t Add) C1 t
  (@additive_terminal_object C Prod t Add) T0 P A B X D b c h)) (@kernel_adjunction_family_func K C
  (@additive_preadditive C Prod t Add) t (@additive_terminal_object C Prod t Add) P (@transf_arrow_diagram_func
  K C B X b)) (@one_cat_native_snake_kernel_first K C (@additive_preadditive C Prod t Add) C1 t
  (@additive_terminal_object C Prod t Add) T0 P Q A B X D b c h) (@one_cat_native_snake_six_term_result K C C1
  Prod t Add T0 P Q N A B X D b c h)) (@finite_arrow_tail_next (Functor_cat K C) (@OneCatNativeExactArrowPair K
  C (@additive_preadditive C Prod t Add) C1 t (@additive_terminal_object C Prod t Add) T0 P Q N) (succ (succ
  zero)) (@kernel_adjunction_family_func K C (@additive_preadditive C Prod t Add) t (@additive_terminal_object C
  Prod t Add) P (@transf_arrow_diagram_func K C B X b)) (@finite_arrow_tail_next (Functor_cat K C)
  (@OneCatNativeExactArrowPair K C (@additive_preadditive C Prod t Add) C1 t (@additive_terminal_object C Prod t
  Add) T0 P Q N) (succ (succ (succ zero))) (@kernel_adjunction_family_func K C (@additive_preadditive C Prod t
  Add) t (@additive_terminal_object C Prod t Add) P (@one_cat_native_snake_alpha_diagram K C
  (@additive_preadditive C Prod t Add) C1 t (@additive_terminal_object C Prod t Add) T0 P A B X D b c h))
  (@kernel_adjunction_family_func K C (@additive_preadditive C Prod t Add) t (@additive_terminal_object C Prod t
  Add) P (@transf_arrow_diagram_func K C B X b)) (@one_cat_native_snake_kernel_first K C (@additive_preadditive
  C Prod t Add) C1 t (@additive_terminal_object C Prod t Add) T0 P Q A B X D b c h)
  (@one_cat_native_snake_six_term_result K C C1 Prod t Add T0 P Q N A B X D b c h)) (@finite_arrow_tail_arrow
  (Functor_cat K C) (@OneCatNativeExactArrowPair K C (@additive_preadditive C Prod t Add) C1 t
  (@additive_terminal_object C Prod t Add) T0 P Q N) (succ (succ (succ zero))) (@kernel_adjunction_family_func K
  C (@additive_preadditive C Prod t Add) t (@additive_terminal_object C Prod t Add) P
  (@one_cat_native_snake_alpha_diagram K C (@additive_preadditive C Prod t Add) C1 t (@additive_terminal_object
  C Prod t Add) T0 P A B X D b c h)) (@kernel_adjunction_family_func K C (@additive_preadditive C Prod t Add) t
  (@additive_terminal_object C Prod t Add) P (@transf_arrow_diagram_func K C B X b))
  (@one_cat_native_snake_kernel_first K C (@additive_preadditive C Prod t Add) C1 t (@additive_terminal_object C
  Prod t Add) T0 P Q A B X D b c h) (@one_cat_native_snake_six_term_result K C C1 Prod t Add T0 P Q N A B X D b
  c h)) (@finite_arrow_tail_rest (Functor_cat K C) (@OneCatNativeExactArrowPair K C (@additive_preadditive C
  Prod t Add) C1 t (@additive_terminal_object C Prod t Add) T0 P Q N) (succ (succ (succ zero)))
  (@kernel_adjunction_family_func K C (@additive_preadditive C Prod t Add) t (@additive_terminal_object C Prod t
  Add) P (@one_cat_native_snake_alpha_diagram K C (@additive_preadditive C Prod t Add) C1 t
  (@additive_terminal_object C Prod t Add) T0 P A B X D b c h)) (@kernel_adjunction_family_func K C
  (@additive_preadditive C Prod t Add) t (@additive_terminal_object C Prod t Add) P (@transf_arrow_diagram_func
  K C B X b)) (@one_cat_native_snake_kernel_first K C (@additive_preadditive C Prod t Add) C1 t
  (@additive_terminal_object C Prod t Add) T0 P Q A B X D b c h) (@one_cat_native_snake_six_term_result K C C1
  Prod t Add T0 P Q N A B X D b c h))) (@finite_arrow_tail_arrow (Functor_cat K C) (@OneCatNativeExactArrowPair
  K C (@additive_preadditive C Prod t Add) C1 t (@additive_terminal_object C Prod t Add) T0 P Q N) (succ (succ
  zero)) (@kernel_adjunction_family_func K C (@additive_preadditive C Prod t Add) t (@additive_terminal_object C
  Prod t Add) P (@transf_arrow_diagram_func K C B X b)) (@finite_arrow_tail_next (Functor_cat K C)
  (@OneCatNativeExactArrowPair K C (@additive_preadditive C Prod t Add) C1 t (@additive_terminal_object C Prod t
  Add) T0 P Q N) (succ (succ (succ zero))) (@kernel_adjunction_family_func K C (@additive_preadditive C Prod t
  Add) t (@additive_terminal_object C Prod t Add) P (@one_cat_native_snake_alpha_diagram K C
  (@additive_preadditive C Prod t Add) C1 t (@additive_terminal_object C Prod t Add) T0 P A B X D b c h))
  (@kernel_adjunction_family_func K C (@additive_preadditive C Prod t Add) t (@additive_terminal_object C Prod t
  Add) P (@transf_arrow_diagram_func K C B X b)) (@one_cat_native_snake_kernel_first K C (@additive_preadditive
  C Prod t Add) C1 t (@additive_terminal_object C Prod t Add) T0 P Q A B X D b c h)
  (@one_cat_native_snake_six_term_result K C C1 Prod t Add T0 P Q N A B X D b c h)) (@finite_arrow_tail_arrow
  (Functor_cat K C) (@OneCatNativeExactArrowPair K C (@additive_preadditive C Prod t Add) C1 t
  (@additive_terminal_object C Prod t Add) T0 P Q N) (succ (succ (succ zero))) (@kernel_adjunction_family_func K
  C (@additive_preadditive C Prod t Add) t (@additive_terminal_object C Prod t Add) P
  (@one_cat_native_snake_alpha_diagram K C (@additive_preadditive C Prod t Add) C1 t (@additive_terminal_object
  C Prod t Add) T0 P A B X D b c h)) (@kernel_adjunction_family_func K C (@additive_preadditive C Prod t Add) t
  (@additive_terminal_object C Prod t Add) P (@transf_arrow_diagram_func K C B X b))
  (@one_cat_native_snake_kernel_first K C (@additive_preadditive C Prod t Add) C1 t (@additive_terminal_object C
  Prod t Add) T0 P Q A B X D b c h) (@one_cat_native_snake_six_term_result K C C1 Prod t Add T0 P Q N A B X D b
  c h)) (@finite_arrow_tail_rest (Functor_cat K C) (@OneCatNativeExactArrowPair K C (@additive_preadditive C
  Prod t Add) C1 t (@additive_terminal_object C Prod t Add) T0 P Q N) (succ (succ (succ zero)))
  (@kernel_adjunction_family_func K C (@additive_preadditive C Prod t Add) t (@additive_terminal_object C Prod t
  Add) P (@one_cat_native_snake_alpha_diagram K C (@additive_preadditive C Prod t Add) C1 t
  (@additive_terminal_object C Prod t Add) T0 P A B X D b c h)) (@kernel_adjunction_family_func K C
  (@additive_preadditive C Prod t Add) t (@additive_terminal_object C Prod t Add) P (@transf_arrow_diagram_func
  K C B X b)) (@one_cat_native_snake_kernel_first K C (@additive_preadditive C Prod t Add) C1 t
  (@additive_terminal_object C Prod t Add) T0 P Q A B X D b c h) (@one_cat_native_snake_six_term_result K C C1
  Prod t Add T0 P Q N A B X D b c h))) (@finite_arrow_tail_rest (Functor_cat K C) (@OneCatNativeExactArrowPair K
  C (@additive_preadditive C Prod t Add) C1 t (@additive_terminal_object C Prod t Add) T0 P Q N) (succ (succ
  zero)) (@kernel_adjunction_family_func K C (@additive_preadditive C Prod t Add) t (@additive_terminal_object C
  Prod t Add) P (@transf_arrow_diagram_func K C B X b)) (@finite_arrow_tail_next (Functor_cat K C)
  (@OneCatNativeExactArrowPair K C (@additive_preadditive C Prod t Add) C1 t (@additive_terminal_object C Prod t
  Add) T0 P Q N) (succ (succ (succ zero))) (@kernel_adjunction_family_func K C (@additive_preadditive C Prod t
  Add) t (@additive_terminal_object C Prod t Add) P (@one_cat_native_snake_alpha_diagram K C
  (@additive_preadditive C Prod t Add) C1 t (@additive_terminal_object C Prod t Add) T0 P A B X D b c h))
  (@kernel_adjunction_family_func K C (@additive_preadditive C Prod t Add) t (@additive_terminal_object C Prod t
  Add) P (@transf_arrow_diagram_func K C B X b)) (@one_cat_native_snake_kernel_first K C (@additive_preadditive
  C Prod t Add) C1 t (@additive_terminal_object C Prod t Add) T0 P Q A B X D b c h)
  (@one_cat_native_snake_six_term_result K C C1 Prod t Add T0 P Q N A B X D b c h)) (@finite_arrow_tail_arrow
  (Functor_cat K C) (@OneCatNativeExactArrowPair K C (@additive_preadditive C Prod t Add) C1 t
  (@additive_terminal_object C Prod t Add) T0 P Q N) (succ (succ (succ zero))) (@kernel_adjunction_family_func K
  C (@additive_preadditive C Prod t Add) t (@additive_terminal_object C Prod t Add) P
  (@one_cat_native_snake_alpha_diagram K C (@additive_preadditive C Prod t Add) C1 t (@additive_terminal_object
  C Prod t Add) T0 P A B X D b c h)) (@kernel_adjunction_family_func K C (@additive_preadditive C Prod t Add) t
  (@additive_terminal_object C Prod t Add) P (@transf_arrow_diagram_func K C B X b))
  (@one_cat_native_snake_kernel_first K C (@additive_preadditive C Prod t Add) C1 t (@additive_terminal_object C
  Prod t Add) T0 P Q A B X D b c h) (@one_cat_native_snake_six_term_result K C C1 Prod t Add T0 P Q N A B X D b
  c h)) (@finite_arrow_tail_rest (Functor_cat K C) (@OneCatNativeExactArrowPair K C (@additive_preadditive C
  Prod t Add) C1 t (@additive_terminal_object C Prod t Add) T0 P Q N) (succ (succ (succ zero)))
  (@kernel_adjunction_family_func K C (@additive_preadditive C Prod t Add) t (@additive_terminal_object C Prod t
  Add) P (@one_cat_native_snake_alpha_diagram K C (@additive_preadditive C Prod t Add) C1 t
  (@additive_terminal_object C Prod t Add) T0 P A B X D b c h)) (@kernel_adjunction_family_func K C
  (@additive_preadditive C Prod t Add) t (@additive_terminal_object C Prod t Add) P (@transf_arrow_diagram_func
  K C B X b)) (@one_cat_native_snake_kernel_first K C (@additive_preadditive C Prod t Add) C1 t
  (@additive_terminal_object C Prod t Add) T0 P Q A B X D b c h) (@one_cat_native_snake_six_term_result K C C1
  Prod t Add T0 P Q N A B X D b c h)))) (@finite_arrow_tail_arrow (Functor_cat K C) (@OneCatNativeExactArrowPair
  K C (@additive_preadditive C Prod t Add) C1 t (@additive_terminal_object C Prod t Add) T0 P Q N) (succ (succ
  zero)) (@kernel_adjunction_family_func K C (@additive_preadditive C Prod t Add) t (@additive_terminal_object C
  Prod t Add) P (@transf_arrow_diagram_func K C B X b)) (@finite_arrow_tail_next (Functor_cat K C)
  (@OneCatNativeExactArrowPair K C (@additive_preadditive C Prod t Add) C1 t (@additive_terminal_object C Prod t
  Add) T0 P Q N) (succ (succ (succ zero))) (@kernel_adjunction_family_func K C (@additive_preadditive C Prod t
  Add) t (@additive_terminal_object C Prod t Add) P (@one_cat_native_snake_alpha_diagram K C
  (@additive_preadditive C Prod t Add) C1 t (@additive_terminal_object C Prod t Add) T0 P A B X D b c h))
  (@kernel_adjunction_family_func K C (@additive_preadditive C Prod t Add) t (@additive_terminal_object C Prod t
  Add) P (@transf_arrow_diagram_func K C B X b)) (@one_cat_native_snake_kernel_first K C (@additive_preadditive
  C Prod t Add) C1 t (@additive_terminal_object C Prod t Add) T0 P Q A B X D b c h)
  (@one_cat_native_snake_six_term_result K C C1 Prod t Add T0 P Q N A B X D b c h)) (@finite_arrow_tail_arrow
  (Functor_cat K C) (@OneCatNativeExactArrowPair K C (@additive_preadditive C Prod t Add) C1 t
  (@additive_terminal_object C Prod t Add) T0 P Q N) (succ (succ (succ zero))) (@kernel_adjunction_family_func K
  C (@additive_preadditive C Prod t Add) t (@additive_terminal_object C Prod t Add) P
  (@one_cat_native_snake_alpha_diagram K C (@additive_preadditive C Prod t Add) C1 t (@additive_terminal_object
  C Prod t Add) T0 P A B X D b c h)) (@kernel_adjunction_family_func K C (@additive_preadditive C Prod t Add) t
  (@additive_terminal_object C Prod t Add) P (@transf_arrow_diagram_func K C B X b))
  (@one_cat_native_snake_kernel_first K C (@additive_preadditive C Prod t Add) C1 t (@additive_terminal_object C
  Prod t Add) T0 P Q A B X D b c h) (@one_cat_native_snake_six_term_result K C C1 Prod t Add T0 P Q N A B X D b
  c h)) (@finite_arrow_tail_rest (Functor_cat K C) (@OneCatNativeExactArrowPair K C (@additive_preadditive C
  Prod t Add) C1 t (@additive_terminal_object C Prod t Add) T0 P Q N) (succ (succ (succ zero)))
  (@kernel_adjunction_family_func K C (@additive_preadditive C Prod t Add) t (@additive_terminal_object C Prod t
  Add) P (@one_cat_native_snake_alpha_diagram K C (@additive_preadditive C Prod t Add) C1 t
  (@additive_terminal_object C Prod t Add) T0 P A B X D b c h)) (@kernel_adjunction_family_func K C
  (@additive_preadditive C Prod t Add) t (@additive_terminal_object C Prod t Add) P (@transf_arrow_diagram_func
  K C B X b)) (@one_cat_native_snake_kernel_first K C (@additive_preadditive C Prod t Add) C1 t
  (@additive_terminal_object C Prod t Add) T0 P Q A B X D b c h) (@one_cat_native_snake_six_term_result K C C1
  Prod t Add T0 P Q N A B X D b c h)))) (@zero_arrow_family_zero_transf K C t (@additive_terminal_object C Prod
  t Add) T0 (@finite_arrow_tail_next (Functor_cat K C) (@OneCatNativeExactArrowPair K C (@additive_preadditive C
  Prod t Add) C1 t (@additive_terminal_object C Prod t Add) T0 P Q N) (succ (succ (succ zero)))
  (@kernel_adjunction_family_func K C (@additive_preadditive C Prod t Add) t (@additive_terminal_object C Prod t
  Add) P (@one_cat_native_snake_alpha_diagram K C (@additive_preadditive C Prod t Add) C1 t
  (@additive_terminal_object C Prod t Add) T0 P A B X D b c h)) (@kernel_adjunction_family_func K C
  (@additive_preadditive C Prod t Add) t (@additive_terminal_object C Prod t Add) P (@transf_arrow_diagram_func
  K C B X b)) (@one_cat_native_snake_kernel_first K C (@additive_preadditive C Prod t Add) C1 t
  (@additive_terminal_object C Prod t Add) T0 P Q A B X D b c h) (@one_cat_native_snake_six_term_result K C C1
  Prod t Add T0 P Q N A B X D b c h)) (@finite_arrow_tail_next (Functor_cat K C) (@OneCatNativeExactArrowPair K
  C (@additive_preadditive C Prod t Add) C1 t (@additive_terminal_object C Prod t Add) T0 P Q N) (succ zero)
  (@finite_arrow_tail_next (Functor_cat K C) (@OneCatNativeExactArrowPair K C (@additive_preadditive C Prod t
  Add) C1 t (@additive_terminal_object C Prod t Add) T0 P Q N) (succ (succ (succ zero)))
  (@kernel_adjunction_family_func K C (@additive_preadditive C Prod t Add) t (@additive_terminal_object C Prod t
  Add) P (@one_cat_native_snake_alpha_diagram K C (@additive_preadditive C Prod t Add) C1 t
  (@additive_terminal_object C Prod t Add) T0 P A B X D b c h)) (@kernel_adjunction_family_func K C
  (@additive_preadditive C Prod t Add) t (@additive_terminal_object C Prod t Add) P (@transf_arrow_diagram_func
  K C B X b)) (@one_cat_native_snake_kernel_first K C (@additive_preadditive C Prod t Add) C1 t
  (@additive_terminal_object C Prod t Add) T0 P Q A B X D b c h) (@one_cat_native_snake_six_term_result K C C1
  Prod t Add T0 P Q N A B X D b c h)) (@finite_arrow_tail_next (Functor_cat K C) (@OneCatNativeExactArrowPair K
  C (@additive_preadditive C Prod t Add) C1 t (@additive_terminal_object C Prod t Add) T0 P Q N) (succ (succ
  zero)) (@kernel_adjunction_family_func K C (@additive_preadditive C Prod t Add) t (@additive_terminal_object C
  Prod t Add) P (@transf_arrow_diagram_func K C B X b)) (@finite_arrow_tail_next (Functor_cat K C)
  (@OneCatNativeExactArrowPair K C (@additive_preadditive C Prod t Add) C1 t (@additive_terminal_object C Prod t
  Add) T0 P Q N) (succ (succ (succ zero))) (@kernel_adjunction_family_func K C (@additive_preadditive C Prod t
  Add) t (@additive_terminal_object C Prod t Add) P (@one_cat_native_snake_alpha_diagram K C
  (@additive_preadditive C Prod t Add) C1 t (@additive_terminal_object C Prod t Add) T0 P A B X D b c h))
  (@kernel_adjunction_family_func K C (@additive_preadditive C Prod t Add) t (@additive_terminal_object C Prod t
  Add) P (@transf_arrow_diagram_func K C B X b)) (@one_cat_native_snake_kernel_first K C (@additive_preadditive
  C Prod t Add) C1 t (@additive_terminal_object C Prod t Add) T0 P Q A B X D b c h)
  (@one_cat_native_snake_six_term_result K C C1 Prod t Add T0 P Q N A B X D b c h)) (@finite_arrow_tail_arrow
  (Functor_cat K C) (@OneCatNativeExactArrowPair K C (@additive_preadditive C Prod t Add) C1 t
  (@additive_terminal_object C Prod t Add) T0 P Q N) (succ (succ (succ zero))) (@kernel_adjunction_family_func K
  C (@additive_preadditive C Prod t Add) t (@additive_terminal_object C Prod t Add) P
  (@one_cat_native_snake_alpha_diagram K C (@additive_preadditive C Prod t Add) C1 t (@additive_terminal_object
  C Prod t Add) T0 P A B X D b c h)) (@kernel_adjunction_family_func K C (@additive_preadditive C Prod t Add) t
  (@additive_terminal_object C Prod t Add) P (@transf_arrow_diagram_func K C B X b))
  (@one_cat_native_snake_kernel_first K C (@additive_preadditive C Prod t Add) C1 t (@additive_terminal_object C
  Prod t Add) T0 P Q A B X D b c h) (@one_cat_native_snake_six_term_result K C C1 Prod t Add T0 P Q N A B X D b
  c h)) (@finite_arrow_tail_rest (Functor_cat K C) (@OneCatNativeExactArrowPair K C (@additive_preadditive C
  Prod t Add) C1 t (@additive_terminal_object C Prod t Add) T0 P Q N) (succ (succ (succ zero)))
  (@kernel_adjunction_family_func K C (@additive_preadditive C Prod t Add) t (@additive_terminal_object C Prod t
  Add) P (@one_cat_native_snake_alpha_diagram K C (@additive_preadditive C Prod t Add) C1 t
  (@additive_terminal_object C Prod t Add) T0 P A B X D b c h)) (@kernel_adjunction_family_func K C
  (@additive_preadditive C Prod t Add) t (@additive_terminal_object C Prod t Add) P (@transf_arrow_diagram_func
  K C B X b)) (@one_cat_native_snake_kernel_first K C (@additive_preadditive C Prod t Add) C1 t
  (@additive_terminal_object C Prod t Add) T0 P Q A B X D b c h) (@one_cat_native_snake_six_term_result K C C1
  Prod t Add T0 P Q N A B X D b c h))) (@finite_arrow_tail_arrow (Functor_cat K C) (@OneCatNativeExactArrowPair
  K C (@additive_preadditive C Prod t Add) C1 t (@additive_terminal_object C Prod t Add) T0 P Q N) (succ (succ
  zero)) (@kernel_adjunction_family_func K C (@additive_preadditive C Prod t Add) t (@additive_terminal_object C
  Prod t Add) P (@transf_arrow_diagram_func K C B X b)) (@finite_arrow_tail_next (Functor_cat K C)
  (@OneCatNativeExactArrowPair K C (@additive_preadditive C Prod t Add) C1 t (@additive_terminal_object C Prod t
  Add) T0 P Q N) (succ (succ (succ zero))) (@kernel_adjunction_family_func K C (@additive_preadditive C Prod t
  Add) t (@additive_terminal_object C Prod t Add) P (@one_cat_native_snake_alpha_diagram K C
  (@additive_preadditive C Prod t Add) C1 t (@additive_terminal_object C Prod t Add) T0 P A B X D b c h))
  (@kernel_adjunction_family_func K C (@additive_preadditive C Prod t Add) t (@additive_terminal_object C Prod t
  Add) P (@transf_arrow_diagram_func K C B X b)) (@one_cat_native_snake_kernel_first K C (@additive_preadditive
  C Prod t Add) C1 t (@additive_terminal_object C Prod t Add) T0 P Q A B X D b c h)
  (@one_cat_native_snake_six_term_result K C C1 Prod t Add T0 P Q N A B X D b c h)) (@finite_arrow_tail_arrow
  (Functor_cat K C) (@OneCatNativeExactArrowPair K C (@additive_preadditive C Prod t Add) C1 t
  (@additive_terminal_object C Prod t Add) T0 P Q N) (succ (succ (succ zero))) (@kernel_adjunction_family_func K
  C (@additive_preadditive C Prod t Add) t (@additive_terminal_object C Prod t Add) P
  (@one_cat_native_snake_alpha_diagram K C (@additive_preadditive C Prod t Add) C1 t (@additive_terminal_object
  C Prod t Add) T0 P A B X D b c h)) (@kernel_adjunction_family_func K C (@additive_preadditive C Prod t Add) t
  (@additive_terminal_object C Prod t Add) P (@transf_arrow_diagram_func K C B X b))
  (@one_cat_native_snake_kernel_first K C (@additive_preadditive C Prod t Add) C1 t (@additive_terminal_object C
  Prod t Add) T0 P Q A B X D b c h) (@one_cat_native_snake_six_term_result K C C1 Prod t Add T0 P Q N A B X D b
  c h)) (@finite_arrow_tail_rest (Functor_cat K C) (@OneCatNativeExactArrowPair K C (@additive_preadditive C
  Prod t Add) C1 t (@additive_terminal_object C Prod t Add) T0 P Q N) (succ (succ (succ zero)))
  (@kernel_adjunction_family_func K C (@additive_preadditive C Prod t Add) t (@additive_terminal_object C Prod t
  Add) P (@one_cat_native_snake_alpha_diagram K C (@additive_preadditive C Prod t Add) C1 t
  (@additive_terminal_object C Prod t Add) T0 P A B X D b c h)) (@kernel_adjunction_family_func K C
  (@additive_preadditive C Prod t Add) t (@additive_terminal_object C Prod t Add) P (@transf_arrow_diagram_func
  K C B X b)) (@one_cat_native_snake_kernel_first K C (@additive_preadditive C Prod t Add) C1 t
  (@additive_terminal_object C Prod t Add) T0 P Q A B X D b c h) (@one_cat_native_snake_six_term_result K C C1
  Prod t Add T0 P Q N A B X D b c h))) (@finite_arrow_tail_rest (Functor_cat K C) (@OneCatNativeExactArrowPair K
  C (@additive_preadditive C Prod t Add) C1 t (@additive_terminal_object C Prod t Add) T0 P Q N) (succ (succ
  zero)) (@kernel_adjunction_family_func K C (@additive_preadditive C Prod t Add) t (@additive_terminal_object C
  Prod t Add) P (@transf_arrow_diagram_func K C B X b)) (@finite_arrow_tail_next (Functor_cat K C)
  (@OneCatNativeExactArrowPair K C (@additive_preadditive C Prod t Add) C1 t (@additive_terminal_object C Prod t
  Add) T0 P Q N) (succ (succ (succ zero))) (@kernel_adjunction_family_func K C (@additive_preadditive C Prod t
  Add) t (@additive_terminal_object C Prod t Add) P (@one_cat_native_snake_alpha_diagram K C
  (@additive_preadditive C Prod t Add) C1 t (@additive_terminal_object C Prod t Add) T0 P A B X D b c h))
  (@kernel_adjunction_family_func K C (@additive_preadditive C Prod t Add) t (@additive_terminal_object C Prod t
  Add) P (@transf_arrow_diagram_func K C B X b)) (@one_cat_native_snake_kernel_first K C (@additive_preadditive
  C Prod t Add) C1 t (@additive_terminal_object C Prod t Add) T0 P Q A B X D b c h)
  (@one_cat_native_snake_six_term_result K C C1 Prod t Add T0 P Q N A B X D b c h)) (@finite_arrow_tail_arrow
  (Functor_cat K C) (@OneCatNativeExactArrowPair K C (@additive_preadditive C Prod t Add) C1 t
  (@additive_terminal_object C Prod t Add) T0 P Q N) (succ (succ (succ zero))) (@kernel_adjunction_family_func K
  C (@additive_preadditive C Prod t Add) t (@additive_terminal_object C Prod t Add) P
  (@one_cat_native_snake_alpha_diagram K C (@additive_preadditive C Prod t Add) C1 t (@additive_terminal_object
  C Prod t Add) T0 P A B X D b c h)) (@kernel_adjunction_family_func K C (@additive_preadditive C Prod t Add) t
  (@additive_terminal_object C Prod t Add) P (@transf_arrow_diagram_func K C B X b))
  (@one_cat_native_snake_kernel_first K C (@additive_preadditive C Prod t Add) C1 t (@additive_terminal_object C
  Prod t Add) T0 P Q A B X D b c h) (@one_cat_native_snake_six_term_result K C C1 Prod t Add T0 P Q N A B X D b
  c h)) (@finite_arrow_tail_rest (Functor_cat K C) (@OneCatNativeExactArrowPair K C (@additive_preadditive C
  Prod t Add) C1 t (@additive_terminal_object C Prod t Add) T0 P Q N) (succ (succ (succ zero)))
  (@kernel_adjunction_family_func K C (@additive_preadditive C Prod t Add) t (@additive_terminal_object C Prod t
  Add) P (@one_cat_native_snake_alpha_diagram K C (@additive_preadditive C Prod t Add) C1 t
  (@additive_terminal_object C Prod t Add) T0 P A B X D b c h)) (@kernel_adjunction_family_func K C
  (@additive_preadditive C Prod t Add) t (@additive_terminal_object C Prod t Add) P (@transf_arrow_diagram_func
  K C B X b)) (@one_cat_native_snake_kernel_first K C (@additive_preadditive C Prod t Add) C1 t
  (@additive_terminal_object C Prod t Add) T0 P Q A B X D b c h) (@one_cat_native_snake_six_term_result K C C1
  Prod t Add T0 P Q N A B X D b c h))))));

// The fourth annotation retains the original native input.
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
  ⊢ (@one_cat_native_exact_arrow_pair_input K C (@additive_preadditive C Prod t Add) C1 t
  (@additive_terminal_object C Prod t Add) T0 P Q N (@finite_arrow_tail_next (Functor_cat K C)
  (@OneCatNativeExactArrowPair K C (@additive_preadditive C Prod t Add) C1 t (@additive_terminal_object C Prod t
  Add) T0 P Q N) (succ (succ zero)) (@kernel_adjunction_family_func K C (@additive_preadditive C Prod t Add) t
  (@additive_terminal_object C Prod t Add) P (@transf_arrow_diagram_func K C B X b)) (@finite_arrow_tail_next
  (Functor_cat K C) (@OneCatNativeExactArrowPair K C (@additive_preadditive C Prod t Add) C1 t
  (@additive_terminal_object C Prod t Add) T0 P Q N) (succ (succ (succ zero))) (@kernel_adjunction_family_func K
  C (@additive_preadditive C Prod t Add) t (@additive_terminal_object C Prod t Add) P
  (@one_cat_native_snake_alpha_diagram K C (@additive_preadditive C Prod t Add) C1 t (@additive_terminal_object
  C Prod t Add) T0 P A B X D b c h)) (@kernel_adjunction_family_func K C (@additive_preadditive C Prod t Add) t
  (@additive_terminal_object C Prod t Add) P (@transf_arrow_diagram_func K C B X b))
  (@one_cat_native_snake_kernel_first K C (@additive_preadditive C Prod t Add) C1 t (@additive_terminal_object C
  Prod t Add) T0 P Q A B X D b c h) (@one_cat_native_snake_six_term_result K C C1 Prod t Add T0 P Q N A B X D b
  c h)) (@finite_arrow_tail_arrow (Functor_cat K C) (@OneCatNativeExactArrowPair K C (@additive_preadditive C
  Prod t Add) C1 t (@additive_terminal_object C Prod t Add) T0 P Q N) (succ (succ (succ zero)))
  (@kernel_adjunction_family_func K C (@additive_preadditive C Prod t Add) t (@additive_terminal_object C Prod t
  Add) P (@one_cat_native_snake_alpha_diagram K C (@additive_preadditive C Prod t Add) C1 t
  (@additive_terminal_object C Prod t Add) T0 P A B X D b c h)) (@kernel_adjunction_family_func K C
  (@additive_preadditive C Prod t Add) t (@additive_terminal_object C Prod t Add) P (@transf_arrow_diagram_func
  K C B X b)) (@one_cat_native_snake_kernel_first K C (@additive_preadditive C Prod t Add) C1 t
  (@additive_terminal_object C Prod t Add) T0 P Q A B X D b c h) (@one_cat_native_snake_six_term_result K C C1
  Prod t Add T0 P Q N A B X D b c h)) (@finite_arrow_tail_rest (Functor_cat K C) (@OneCatNativeExactArrowPair K
  C (@additive_preadditive C Prod t Add) C1 t (@additive_terminal_object C Prod t Add) T0 P Q N) (succ (succ
  (succ zero))) (@kernel_adjunction_family_func K C (@additive_preadditive C Prod t Add) t
  (@additive_terminal_object C Prod t Add) P (@one_cat_native_snake_alpha_diagram K C (@additive_preadditive C
  Prod t Add) C1 t (@additive_terminal_object C Prod t Add) T0 P A B X D b c h)) (@kernel_adjunction_family_func
  K C (@additive_preadditive C Prod t Add) t (@additive_terminal_object C Prod t Add) P
  (@transf_arrow_diagram_func K C B X b)) (@one_cat_native_snake_kernel_first K C (@additive_preadditive C Prod
  t Add) C1 t (@additive_terminal_object C Prod t Add) T0 P Q A B X D b c h)
  (@one_cat_native_snake_six_term_result K C C1 Prod t Add T0 P Q N A B X D b c h))) (@finite_arrow_tail_next
  (Functor_cat K C) (@OneCatNativeExactArrowPair K C (@additive_preadditive C Prod t Add) C1 t
  (@additive_terminal_object C Prod t Add) T0 P Q N) (succ zero) (@finite_arrow_tail_next (Functor_cat K C)
  (@OneCatNativeExactArrowPair K C (@additive_preadditive C Prod t Add) C1 t (@additive_terminal_object C Prod t
  Add) T0 P Q N) (succ (succ (succ zero))) (@kernel_adjunction_family_func K C (@additive_preadditive C Prod t
  Add) t (@additive_terminal_object C Prod t Add) P (@one_cat_native_snake_alpha_diagram K C
  (@additive_preadditive C Prod t Add) C1 t (@additive_terminal_object C Prod t Add) T0 P A B X D b c h))
  (@kernel_adjunction_family_func K C (@additive_preadditive C Prod t Add) t (@additive_terminal_object C Prod t
  Add) P (@transf_arrow_diagram_func K C B X b)) (@one_cat_native_snake_kernel_first K C (@additive_preadditive
  C Prod t Add) C1 t (@additive_terminal_object C Prod t Add) T0 P Q A B X D b c h)
  (@one_cat_native_snake_six_term_result K C C1 Prod t Add T0 P Q N A B X D b c h)) (@finite_arrow_tail_next
  (Functor_cat K C) (@OneCatNativeExactArrowPair K C (@additive_preadditive C Prod t Add) C1 t
  (@additive_terminal_object C Prod t Add) T0 P Q N) (succ (succ zero)) (@kernel_adjunction_family_func K C
  (@additive_preadditive C Prod t Add) t (@additive_terminal_object C Prod t Add) P (@transf_arrow_diagram_func
  K C B X b)) (@finite_arrow_tail_next (Functor_cat K C) (@OneCatNativeExactArrowPair K C (@additive_preadditive
  C Prod t Add) C1 t (@additive_terminal_object C Prod t Add) T0 P Q N) (succ (succ (succ zero)))
  (@kernel_adjunction_family_func K C (@additive_preadditive C Prod t Add) t (@additive_terminal_object C Prod t
  Add) P (@one_cat_native_snake_alpha_diagram K C (@additive_preadditive C Prod t Add) C1 t
  (@additive_terminal_object C Prod t Add) T0 P A B X D b c h)) (@kernel_adjunction_family_func K C
  (@additive_preadditive C Prod t Add) t (@additive_terminal_object C Prod t Add) P (@transf_arrow_diagram_func
  K C B X b)) (@one_cat_native_snake_kernel_first K C (@additive_preadditive C Prod t Add) C1 t
  (@additive_terminal_object C Prod t Add) T0 P Q A B X D b c h) (@one_cat_native_snake_six_term_result K C C1
  Prod t Add T0 P Q N A B X D b c h)) (@finite_arrow_tail_arrow (Functor_cat K C) (@OneCatNativeExactArrowPair K
  C (@additive_preadditive C Prod t Add) C1 t (@additive_terminal_object C Prod t Add) T0 P Q N) (succ (succ
  (succ zero))) (@kernel_adjunction_family_func K C (@additive_preadditive C Prod t Add) t
  (@additive_terminal_object C Prod t Add) P (@one_cat_native_snake_alpha_diagram K C (@additive_preadditive C
  Prod t Add) C1 t (@additive_terminal_object C Prod t Add) T0 P A B X D b c h)) (@kernel_adjunction_family_func
  K C (@additive_preadditive C Prod t Add) t (@additive_terminal_object C Prod t Add) P
  (@transf_arrow_diagram_func K C B X b)) (@one_cat_native_snake_kernel_first K C (@additive_preadditive C Prod
  t Add) C1 t (@additive_terminal_object C Prod t Add) T0 P Q A B X D b c h)
  (@one_cat_native_snake_six_term_result K C C1 Prod t Add T0 P Q N A B X D b c h)) (@finite_arrow_tail_rest
  (Functor_cat K C) (@OneCatNativeExactArrowPair K C (@additive_preadditive C Prod t Add) C1 t
  (@additive_terminal_object C Prod t Add) T0 P Q N) (succ (succ (succ zero))) (@kernel_adjunction_family_func K
  C (@additive_preadditive C Prod t Add) t (@additive_terminal_object C Prod t Add) P
  (@one_cat_native_snake_alpha_diagram K C (@additive_preadditive C Prod t Add) C1 t (@additive_terminal_object
  C Prod t Add) T0 P A B X D b c h)) (@kernel_adjunction_family_func K C (@additive_preadditive C Prod t Add) t
  (@additive_terminal_object C Prod t Add) P (@transf_arrow_diagram_func K C B X b))
  (@one_cat_native_snake_kernel_first K C (@additive_preadditive C Prod t Add) C1 t (@additive_terminal_object C
  Prod t Add) T0 P Q A B X D b c h) (@one_cat_native_snake_six_term_result K C C1 Prod t Add T0 P Q N A B X D b
  c h))) (@finite_arrow_tail_arrow (Functor_cat K C) (@OneCatNativeExactArrowPair K C (@additive_preadditive C
  Prod t Add) C1 t (@additive_terminal_object C Prod t Add) T0 P Q N) (succ (succ zero))
  (@kernel_adjunction_family_func K C (@additive_preadditive C Prod t Add) t (@additive_terminal_object C Prod t
  Add) P (@transf_arrow_diagram_func K C B X b)) (@finite_arrow_tail_next (Functor_cat K C)
  (@OneCatNativeExactArrowPair K C (@additive_preadditive C Prod t Add) C1 t (@additive_terminal_object C Prod t
  Add) T0 P Q N) (succ (succ (succ zero))) (@kernel_adjunction_family_func K C (@additive_preadditive C Prod t
  Add) t (@additive_terminal_object C Prod t Add) P (@one_cat_native_snake_alpha_diagram K C
  (@additive_preadditive C Prod t Add) C1 t (@additive_terminal_object C Prod t Add) T0 P A B X D b c h))
  (@kernel_adjunction_family_func K C (@additive_preadditive C Prod t Add) t (@additive_terminal_object C Prod t
  Add) P (@transf_arrow_diagram_func K C B X b)) (@one_cat_native_snake_kernel_first K C (@additive_preadditive
  C Prod t Add) C1 t (@additive_terminal_object C Prod t Add) T0 P Q A B X D b c h)
  (@one_cat_native_snake_six_term_result K C C1 Prod t Add T0 P Q N A B X D b c h)) (@finite_arrow_tail_arrow
  (Functor_cat K C) (@OneCatNativeExactArrowPair K C (@additive_preadditive C Prod t Add) C1 t
  (@additive_terminal_object C Prod t Add) T0 P Q N) (succ (succ (succ zero))) (@kernel_adjunction_family_func K
  C (@additive_preadditive C Prod t Add) t (@additive_terminal_object C Prod t Add) P
  (@one_cat_native_snake_alpha_diagram K C (@additive_preadditive C Prod t Add) C1 t (@additive_terminal_object
  C Prod t Add) T0 P A B X D b c h)) (@kernel_adjunction_family_func K C (@additive_preadditive C Prod t Add) t
  (@additive_terminal_object C Prod t Add) P (@transf_arrow_diagram_func K C B X b))
  (@one_cat_native_snake_kernel_first K C (@additive_preadditive C Prod t Add) C1 t (@additive_terminal_object C
  Prod t Add) T0 P Q A B X D b c h) (@one_cat_native_snake_six_term_result K C C1 Prod t Add T0 P Q N A B X D b
  c h)) (@finite_arrow_tail_rest (Functor_cat K C) (@OneCatNativeExactArrowPair K C (@additive_preadditive C
  Prod t Add) C1 t (@additive_terminal_object C Prod t Add) T0 P Q N) (succ (succ (succ zero)))
  (@kernel_adjunction_family_func K C (@additive_preadditive C Prod t Add) t (@additive_terminal_object C Prod t
  Add) P (@one_cat_native_snake_alpha_diagram K C (@additive_preadditive C Prod t Add) C1 t
  (@additive_terminal_object C Prod t Add) T0 P A B X D b c h)) (@kernel_adjunction_family_func K C
  (@additive_preadditive C Prod t Add) t (@additive_terminal_object C Prod t Add) P (@transf_arrow_diagram_func
  K C B X b)) (@one_cat_native_snake_kernel_first K C (@additive_preadditive C Prod t Add) C1 t
  (@additive_terminal_object C Prod t Add) T0 P Q A B X D b c h) (@one_cat_native_snake_six_term_result K C C1
  Prod t Add T0 P Q N A B X D b c h))) (@finite_arrow_tail_rest (Functor_cat K C) (@OneCatNativeExactArrowPair K
  C (@additive_preadditive C Prod t Add) C1 t (@additive_terminal_object C Prod t Add) T0 P Q N) (succ (succ
  zero)) (@kernel_adjunction_family_func K C (@additive_preadditive C Prod t Add) t (@additive_terminal_object C
  Prod t Add) P (@transf_arrow_diagram_func K C B X b)) (@finite_arrow_tail_next (Functor_cat K C)
  (@OneCatNativeExactArrowPair K C (@additive_preadditive C Prod t Add) C1 t (@additive_terminal_object C Prod t
  Add) T0 P Q N) (succ (succ (succ zero))) (@kernel_adjunction_family_func K C (@additive_preadditive C Prod t
  Add) t (@additive_terminal_object C Prod t Add) P (@one_cat_native_snake_alpha_diagram K C
  (@additive_preadditive C Prod t Add) C1 t (@additive_terminal_object C Prod t Add) T0 P A B X D b c h))
  (@kernel_adjunction_family_func K C (@additive_preadditive C Prod t Add) t (@additive_terminal_object C Prod t
  Add) P (@transf_arrow_diagram_func K C B X b)) (@one_cat_native_snake_kernel_first K C (@additive_preadditive
  C Prod t Add) C1 t (@additive_terminal_object C Prod t Add) T0 P Q A B X D b c h)
  (@one_cat_native_snake_six_term_result K C C1 Prod t Add T0 P Q N A B X D b c h)) (@finite_arrow_tail_arrow
  (Functor_cat K C) (@OneCatNativeExactArrowPair K C (@additive_preadditive C Prod t Add) C1 t
  (@additive_terminal_object C Prod t Add) T0 P Q N) (succ (succ (succ zero))) (@kernel_adjunction_family_func K
  C (@additive_preadditive C Prod t Add) t (@additive_terminal_object C Prod t Add) P
  (@one_cat_native_snake_alpha_diagram K C (@additive_preadditive C Prod t Add) C1 t (@additive_terminal_object
  C Prod t Add) T0 P A B X D b c h)) (@kernel_adjunction_family_func K C (@additive_preadditive C Prod t Add) t
  (@additive_terminal_object C Prod t Add) P (@transf_arrow_diagram_func K C B X b))
  (@one_cat_native_snake_kernel_first K C (@additive_preadditive C Prod t Add) C1 t (@additive_terminal_object C
  Prod t Add) T0 P Q A B X D b c h) (@one_cat_native_snake_six_term_result K C C1 Prod t Add T0 P Q N A B X D b
  c h)) (@finite_arrow_tail_rest (Functor_cat K C) (@OneCatNativeExactArrowPair K C (@additive_preadditive C
  Prod t Add) C1 t (@additive_terminal_object C Prod t Add) T0 P Q N) (succ (succ (succ zero)))
  (@kernel_adjunction_family_func K C (@additive_preadditive C Prod t Add) t (@additive_terminal_object C Prod t
  Add) P (@one_cat_native_snake_alpha_diagram K C (@additive_preadditive C Prod t Add) C1 t
  (@additive_terminal_object C Prod t Add) T0 P A B X D b c h)) (@kernel_adjunction_family_func K C
  (@additive_preadditive C Prod t Add) t (@additive_terminal_object C Prod t Add) P (@transf_arrow_diagram_func
  K C B X b)) (@one_cat_native_snake_kernel_first K C (@additive_preadditive C Prod t Add) C1 t
  (@additive_terminal_object C Prod t Add) T0 P Q A B X D b c h) (@one_cat_native_snake_six_term_result K C C1
  Prod t Add T0 P Q N A B X D b c h)))) (@finite_arrow_tail_next (Functor_cat K C) (@OneCatNativeExactArrowPair
  K C (@additive_preadditive C Prod t Add) C1 t (@additive_terminal_object C Prod t Add) T0 P Q N) zero
  (@finite_arrow_tail_next (Functor_cat K C) (@OneCatNativeExactArrowPair K C (@additive_preadditive C Prod t
  Add) C1 t (@additive_terminal_object C Prod t Add) T0 P Q N) (succ (succ zero))
  (@kernel_adjunction_family_func K C (@additive_preadditive C Prod t Add) t (@additive_terminal_object C Prod t
  Add) P (@transf_arrow_diagram_func K C B X b)) (@finite_arrow_tail_next (Functor_cat K C)
  (@OneCatNativeExactArrowPair K C (@additive_preadditive C Prod t Add) C1 t (@additive_terminal_object C Prod t
  Add) T0 P Q N) (succ (succ (succ zero))) (@kernel_adjunction_family_func K C (@additive_preadditive C Prod t
  Add) t (@additive_terminal_object C Prod t Add) P (@one_cat_native_snake_alpha_diagram K C
  (@additive_preadditive C Prod t Add) C1 t (@additive_terminal_object C Prod t Add) T0 P A B X D b c h))
  (@kernel_adjunction_family_func K C (@additive_preadditive C Prod t Add) t (@additive_terminal_object C Prod t
  Add) P (@transf_arrow_diagram_func K C B X b)) (@one_cat_native_snake_kernel_first K C (@additive_preadditive
  C Prod t Add) C1 t (@additive_terminal_object C Prod t Add) T0 P Q A B X D b c h)
  (@one_cat_native_snake_six_term_result K C C1 Prod t Add T0 P Q N A B X D b c h)) (@finite_arrow_tail_arrow
  (Functor_cat K C) (@OneCatNativeExactArrowPair K C (@additive_preadditive C Prod t Add) C1 t
  (@additive_terminal_object C Prod t Add) T0 P Q N) (succ (succ (succ zero))) (@kernel_adjunction_family_func K
  C (@additive_preadditive C Prod t Add) t (@additive_terminal_object C Prod t Add) P
  (@one_cat_native_snake_alpha_diagram K C (@additive_preadditive C Prod t Add) C1 t (@additive_terminal_object
  C Prod t Add) T0 P A B X D b c h)) (@kernel_adjunction_family_func K C (@additive_preadditive C Prod t Add) t
  (@additive_terminal_object C Prod t Add) P (@transf_arrow_diagram_func K C B X b))
  (@one_cat_native_snake_kernel_first K C (@additive_preadditive C Prod t Add) C1 t (@additive_terminal_object C
  Prod t Add) T0 P Q A B X D b c h) (@one_cat_native_snake_six_term_result K C C1 Prod t Add T0 P Q N A B X D b
  c h)) (@finite_arrow_tail_rest (Functor_cat K C) (@OneCatNativeExactArrowPair K C (@additive_preadditive C
  Prod t Add) C1 t (@additive_terminal_object C Prod t Add) T0 P Q N) (succ (succ (succ zero)))
  (@kernel_adjunction_family_func K C (@additive_preadditive C Prod t Add) t (@additive_terminal_object C Prod t
  Add) P (@one_cat_native_snake_alpha_diagram K C (@additive_preadditive C Prod t Add) C1 t
  (@additive_terminal_object C Prod t Add) T0 P A B X D b c h)) (@kernel_adjunction_family_func K C
  (@additive_preadditive C Prod t Add) t (@additive_terminal_object C Prod t Add) P (@transf_arrow_diagram_func
  K C B X b)) (@one_cat_native_snake_kernel_first K C (@additive_preadditive C Prod t Add) C1 t
  (@additive_terminal_object C Prod t Add) T0 P Q A B X D b c h) (@one_cat_native_snake_six_term_result K C C1
  Prod t Add T0 P Q N A B X D b c h))) (@finite_arrow_tail_next (Functor_cat K C) (@OneCatNativeExactArrowPair K
  C (@additive_preadditive C Prod t Add) C1 t (@additive_terminal_object C Prod t Add) T0 P Q N) (succ zero)
  (@finite_arrow_tail_next (Functor_cat K C) (@OneCatNativeExactArrowPair K C (@additive_preadditive C Prod t
  Add) C1 t (@additive_terminal_object C Prod t Add) T0 P Q N) (succ (succ (succ zero)))
  (@kernel_adjunction_family_func K C (@additive_preadditive C Prod t Add) t (@additive_terminal_object C Prod t
  Add) P (@one_cat_native_snake_alpha_diagram K C (@additive_preadditive C Prod t Add) C1 t
  (@additive_terminal_object C Prod t Add) T0 P A B X D b c h)) (@kernel_adjunction_family_func K C
  (@additive_preadditive C Prod t Add) t (@additive_terminal_object C Prod t Add) P (@transf_arrow_diagram_func
  K C B X b)) (@one_cat_native_snake_kernel_first K C (@additive_preadditive C Prod t Add) C1 t
  (@additive_terminal_object C Prod t Add) T0 P Q A B X D b c h) (@one_cat_native_snake_six_term_result K C C1
  Prod t Add T0 P Q N A B X D b c h)) (@finite_arrow_tail_next (Functor_cat K C) (@OneCatNativeExactArrowPair K
  C (@additive_preadditive C Prod t Add) C1 t (@additive_terminal_object C Prod t Add) T0 P Q N) (succ (succ
  zero)) (@kernel_adjunction_family_func K C (@additive_preadditive C Prod t Add) t (@additive_terminal_object C
  Prod t Add) P (@transf_arrow_diagram_func K C B X b)) (@finite_arrow_tail_next (Functor_cat K C)
  (@OneCatNativeExactArrowPair K C (@additive_preadditive C Prod t Add) C1 t (@additive_terminal_object C Prod t
  Add) T0 P Q N) (succ (succ (succ zero))) (@kernel_adjunction_family_func K C (@additive_preadditive C Prod t
  Add) t (@additive_terminal_object C Prod t Add) P (@one_cat_native_snake_alpha_diagram K C
  (@additive_preadditive C Prod t Add) C1 t (@additive_terminal_object C Prod t Add) T0 P A B X D b c h))
  (@kernel_adjunction_family_func K C (@additive_preadditive C Prod t Add) t (@additive_terminal_object C Prod t
  Add) P (@transf_arrow_diagram_func K C B X b)) (@one_cat_native_snake_kernel_first K C (@additive_preadditive
  C Prod t Add) C1 t (@additive_terminal_object C Prod t Add) T0 P Q A B X D b c h)
  (@one_cat_native_snake_six_term_result K C C1 Prod t Add T0 P Q N A B X D b c h)) (@finite_arrow_tail_arrow
  (Functor_cat K C) (@OneCatNativeExactArrowPair K C (@additive_preadditive C Prod t Add) C1 t
  (@additive_terminal_object C Prod t Add) T0 P Q N) (succ (succ (succ zero))) (@kernel_adjunction_family_func K
  C (@additive_preadditive C Prod t Add) t (@additive_terminal_object C Prod t Add) P
  (@one_cat_native_snake_alpha_diagram K C (@additive_preadditive C Prod t Add) C1 t (@additive_terminal_object
  C Prod t Add) T0 P A B X D b c h)) (@kernel_adjunction_family_func K C (@additive_preadditive C Prod t Add) t
  (@additive_terminal_object C Prod t Add) P (@transf_arrow_diagram_func K C B X b))
  (@one_cat_native_snake_kernel_first K C (@additive_preadditive C Prod t Add) C1 t (@additive_terminal_object C
  Prod t Add) T0 P Q A B X D b c h) (@one_cat_native_snake_six_term_result K C C1 Prod t Add T0 P Q N A B X D b
  c h)) (@finite_arrow_tail_rest (Functor_cat K C) (@OneCatNativeExactArrowPair K C (@additive_preadditive C
  Prod t Add) C1 t (@additive_terminal_object C Prod t Add) T0 P Q N) (succ (succ (succ zero)))
  (@kernel_adjunction_family_func K C (@additive_preadditive C Prod t Add) t (@additive_terminal_object C Prod t
  Add) P (@one_cat_native_snake_alpha_diagram K C (@additive_preadditive C Prod t Add) C1 t
  (@additive_terminal_object C Prod t Add) T0 P A B X D b c h)) (@kernel_adjunction_family_func K C
  (@additive_preadditive C Prod t Add) t (@additive_terminal_object C Prod t Add) P (@transf_arrow_diagram_func
  K C B X b)) (@one_cat_native_snake_kernel_first K C (@additive_preadditive C Prod t Add) C1 t
  (@additive_terminal_object C Prod t Add) T0 P Q A B X D b c h) (@one_cat_native_snake_six_term_result K C C1
  Prod t Add T0 P Q N A B X D b c h))) (@finite_arrow_tail_arrow (Functor_cat K C) (@OneCatNativeExactArrowPair
  K C (@additive_preadditive C Prod t Add) C1 t (@additive_terminal_object C Prod t Add) T0 P Q N) (succ (succ
  zero)) (@kernel_adjunction_family_func K C (@additive_preadditive C Prod t Add) t (@additive_terminal_object C
  Prod t Add) P (@transf_arrow_diagram_func K C B X b)) (@finite_arrow_tail_next (Functor_cat K C)
  (@OneCatNativeExactArrowPair K C (@additive_preadditive C Prod t Add) C1 t (@additive_terminal_object C Prod t
  Add) T0 P Q N) (succ (succ (succ zero))) (@kernel_adjunction_family_func K C (@additive_preadditive C Prod t
  Add) t (@additive_terminal_object C Prod t Add) P (@one_cat_native_snake_alpha_diagram K C
  (@additive_preadditive C Prod t Add) C1 t (@additive_terminal_object C Prod t Add) T0 P A B X D b c h))
  (@kernel_adjunction_family_func K C (@additive_preadditive C Prod t Add) t (@additive_terminal_object C Prod t
  Add) P (@transf_arrow_diagram_func K C B X b)) (@one_cat_native_snake_kernel_first K C (@additive_preadditive
  C Prod t Add) C1 t (@additive_terminal_object C Prod t Add) T0 P Q A B X D b c h)
  (@one_cat_native_snake_six_term_result K C C1 Prod t Add T0 P Q N A B X D b c h)) (@finite_arrow_tail_arrow
  (Functor_cat K C) (@OneCatNativeExactArrowPair K C (@additive_preadditive C Prod t Add) C1 t
  (@additive_terminal_object C Prod t Add) T0 P Q N) (succ (succ (succ zero))) (@kernel_adjunction_family_func K
  C (@additive_preadditive C Prod t Add) t (@additive_terminal_object C Prod t Add) P
  (@one_cat_native_snake_alpha_diagram K C (@additive_preadditive C Prod t Add) C1 t (@additive_terminal_object
  C Prod t Add) T0 P A B X D b c h)) (@kernel_adjunction_family_func K C (@additive_preadditive C Prod t Add) t
  (@additive_terminal_object C Prod t Add) P (@transf_arrow_diagram_func K C B X b))
  (@one_cat_native_snake_kernel_first K C (@additive_preadditive C Prod t Add) C1 t (@additive_terminal_object C
  Prod t Add) T0 P Q A B X D b c h) (@one_cat_native_snake_six_term_result K C C1 Prod t Add T0 P Q N A B X D b
  c h)) (@finite_arrow_tail_rest (Functor_cat K C) (@OneCatNativeExactArrowPair K C (@additive_preadditive C
  Prod t Add) C1 t (@additive_terminal_object C Prod t Add) T0 P Q N) (succ (succ (succ zero)))
  (@kernel_adjunction_family_func K C (@additive_preadditive C Prod t Add) t (@additive_terminal_object C Prod t
  Add) P (@one_cat_native_snake_alpha_diagram K C (@additive_preadditive C Prod t Add) C1 t
  (@additive_terminal_object C Prod t Add) T0 P A B X D b c h)) (@kernel_adjunction_family_func K C
  (@additive_preadditive C Prod t Add) t (@additive_terminal_object C Prod t Add) P (@transf_arrow_diagram_func
  K C B X b)) (@one_cat_native_snake_kernel_first K C (@additive_preadditive C Prod t Add) C1 t
  (@additive_terminal_object C Prod t Add) T0 P Q A B X D b c h) (@one_cat_native_snake_six_term_result K C C1
  Prod t Add T0 P Q N A B X D b c h))) (@finite_arrow_tail_rest (Functor_cat K C) (@OneCatNativeExactArrowPair K
  C (@additive_preadditive C Prod t Add) C1 t (@additive_terminal_object C Prod t Add) T0 P Q N) (succ (succ
  zero)) (@kernel_adjunction_family_func K C (@additive_preadditive C Prod t Add) t (@additive_terminal_object C
  Prod t Add) P (@transf_arrow_diagram_func K C B X b)) (@finite_arrow_tail_next (Functor_cat K C)
  (@OneCatNativeExactArrowPair K C (@additive_preadditive C Prod t Add) C1 t (@additive_terminal_object C Prod t
  Add) T0 P Q N) (succ (succ (succ zero))) (@kernel_adjunction_family_func K C (@additive_preadditive C Prod t
  Add) t (@additive_terminal_object C Prod t Add) P (@one_cat_native_snake_alpha_diagram K C
  (@additive_preadditive C Prod t Add) C1 t (@additive_terminal_object C Prod t Add) T0 P A B X D b c h))
  (@kernel_adjunction_family_func K C (@additive_preadditive C Prod t Add) t (@additive_terminal_object C Prod t
  Add) P (@transf_arrow_diagram_func K C B X b)) (@one_cat_native_snake_kernel_first K C (@additive_preadditive
  C Prod t Add) C1 t (@additive_terminal_object C Prod t Add) T0 P Q A B X D b c h)
  (@one_cat_native_snake_six_term_result K C C1 Prod t Add T0 P Q N A B X D b c h)) (@finite_arrow_tail_arrow
  (Functor_cat K C) (@OneCatNativeExactArrowPair K C (@additive_preadditive C Prod t Add) C1 t
  (@additive_terminal_object C Prod t Add) T0 P Q N) (succ (succ (succ zero))) (@kernel_adjunction_family_func K
  C (@additive_preadditive C Prod t Add) t (@additive_terminal_object C Prod t Add) P
  (@one_cat_native_snake_alpha_diagram K C (@additive_preadditive C Prod t Add) C1 t (@additive_terminal_object
  C Prod t Add) T0 P A B X D b c h)) (@kernel_adjunction_family_func K C (@additive_preadditive C Prod t Add) t
  (@additive_terminal_object C Prod t Add) P (@transf_arrow_diagram_func K C B X b))
  (@one_cat_native_snake_kernel_first K C (@additive_preadditive C Prod t Add) C1 t (@additive_terminal_object C
  Prod t Add) T0 P Q A B X D b c h) (@one_cat_native_snake_six_term_result K C C1 Prod t Add T0 P Q N A B X D b
  c h)) (@finite_arrow_tail_rest (Functor_cat K C) (@OneCatNativeExactArrowPair K C (@additive_preadditive C
  Prod t Add) C1 t (@additive_terminal_object C Prod t Add) T0 P Q N) (succ (succ (succ zero)))
  (@kernel_adjunction_family_func K C (@additive_preadditive C Prod t Add) t (@additive_terminal_object C Prod t
  Add) P (@one_cat_native_snake_alpha_diagram K C (@additive_preadditive C Prod t Add) C1 t
  (@additive_terminal_object C Prod t Add) T0 P A B X D b c h)) (@kernel_adjunction_family_func K C
  (@additive_preadditive C Prod t Add) t (@additive_terminal_object C Prod t Add) P (@transf_arrow_diagram_func
  K C B X b)) (@one_cat_native_snake_kernel_first K C (@additive_preadditive C Prod t Add) C1 t
  (@additive_terminal_object C Prod t Add) T0 P Q A B X D b c h) (@one_cat_native_snake_six_term_result K C C1
  Prod t Add T0 P Q N A B X D b c h)))) (@finite_arrow_tail_arrow (Functor_cat K C) (@OneCatNativeExactArrowPair
  K C (@additive_preadditive C Prod t Add) C1 t (@additive_terminal_object C Prod t Add) T0 P Q N) (succ zero)
  (@finite_arrow_tail_next (Functor_cat K C) (@OneCatNativeExactArrowPair K C (@additive_preadditive C Prod t
  Add) C1 t (@additive_terminal_object C Prod t Add) T0 P Q N) (succ (succ (succ zero)))
  (@kernel_adjunction_family_func K C (@additive_preadditive C Prod t Add) t (@additive_terminal_object C Prod t
  Add) P (@one_cat_native_snake_alpha_diagram K C (@additive_preadditive C Prod t Add) C1 t
  (@additive_terminal_object C Prod t Add) T0 P A B X D b c h)) (@kernel_adjunction_family_func K C
  (@additive_preadditive C Prod t Add) t (@additive_terminal_object C Prod t Add) P (@transf_arrow_diagram_func
  K C B X b)) (@one_cat_native_snake_kernel_first K C (@additive_preadditive C Prod t Add) C1 t
  (@additive_terminal_object C Prod t Add) T0 P Q A B X D b c h) (@one_cat_native_snake_six_term_result K C C1
  Prod t Add T0 P Q N A B X D b c h)) (@finite_arrow_tail_next (Functor_cat K C) (@OneCatNativeExactArrowPair K
  C (@additive_preadditive C Prod t Add) C1 t (@additive_terminal_object C Prod t Add) T0 P Q N) (succ (succ
  zero)) (@kernel_adjunction_family_func K C (@additive_preadditive C Prod t Add) t (@additive_terminal_object C
  Prod t Add) P (@transf_arrow_diagram_func K C B X b)) (@finite_arrow_tail_next (Functor_cat K C)
  (@OneCatNativeExactArrowPair K C (@additive_preadditive C Prod t Add) C1 t (@additive_terminal_object C Prod t
  Add) T0 P Q N) (succ (succ (succ zero))) (@kernel_adjunction_family_func K C (@additive_preadditive C Prod t
  Add) t (@additive_terminal_object C Prod t Add) P (@one_cat_native_snake_alpha_diagram K C
  (@additive_preadditive C Prod t Add) C1 t (@additive_terminal_object C Prod t Add) T0 P A B X D b c h))
  (@kernel_adjunction_family_func K C (@additive_preadditive C Prod t Add) t (@additive_terminal_object C Prod t
  Add) P (@transf_arrow_diagram_func K C B X b)) (@one_cat_native_snake_kernel_first K C (@additive_preadditive
  C Prod t Add) C1 t (@additive_terminal_object C Prod t Add) T0 P Q A B X D b c h)
  (@one_cat_native_snake_six_term_result K C C1 Prod t Add T0 P Q N A B X D b c h)) (@finite_arrow_tail_arrow
  (Functor_cat K C) (@OneCatNativeExactArrowPair K C (@additive_preadditive C Prod t Add) C1 t
  (@additive_terminal_object C Prod t Add) T0 P Q N) (succ (succ (succ zero))) (@kernel_adjunction_family_func K
  C (@additive_preadditive C Prod t Add) t (@additive_terminal_object C Prod t Add) P
  (@one_cat_native_snake_alpha_diagram K C (@additive_preadditive C Prod t Add) C1 t (@additive_terminal_object
  C Prod t Add) T0 P A B X D b c h)) (@kernel_adjunction_family_func K C (@additive_preadditive C Prod t Add) t
  (@additive_terminal_object C Prod t Add) P (@transf_arrow_diagram_func K C B X b))
  (@one_cat_native_snake_kernel_first K C (@additive_preadditive C Prod t Add) C1 t (@additive_terminal_object C
  Prod t Add) T0 P Q A B X D b c h) (@one_cat_native_snake_six_term_result K C C1 Prod t Add T0 P Q N A B X D b
  c h)) (@finite_arrow_tail_rest (Functor_cat K C) (@OneCatNativeExactArrowPair K C (@additive_preadditive C
  Prod t Add) C1 t (@additive_terminal_object C Prod t Add) T0 P Q N) (succ (succ (succ zero)))
  (@kernel_adjunction_family_func K C (@additive_preadditive C Prod t Add) t (@additive_terminal_object C Prod t
  Add) P (@one_cat_native_snake_alpha_diagram K C (@additive_preadditive C Prod t Add) C1 t
  (@additive_terminal_object C Prod t Add) T0 P A B X D b c h)) (@kernel_adjunction_family_func K C
  (@additive_preadditive C Prod t Add) t (@additive_terminal_object C Prod t Add) P (@transf_arrow_diagram_func
  K C B X b)) (@one_cat_native_snake_kernel_first K C (@additive_preadditive C Prod t Add) C1 t
  (@additive_terminal_object C Prod t Add) T0 P Q A B X D b c h) (@one_cat_native_snake_six_term_result K C C1
  Prod t Add T0 P Q N A B X D b c h))) (@finite_arrow_tail_arrow (Functor_cat K C) (@OneCatNativeExactArrowPair
  K C (@additive_preadditive C Prod t Add) C1 t (@additive_terminal_object C Prod t Add) T0 P Q N) (succ (succ
  zero)) (@kernel_adjunction_family_func K C (@additive_preadditive C Prod t Add) t (@additive_terminal_object C
  Prod t Add) P (@transf_arrow_diagram_func K C B X b)) (@finite_arrow_tail_next (Functor_cat K C)
  (@OneCatNativeExactArrowPair K C (@additive_preadditive C Prod t Add) C1 t (@additive_terminal_object C Prod t
  Add) T0 P Q N) (succ (succ (succ zero))) (@kernel_adjunction_family_func K C (@additive_preadditive C Prod t
  Add) t (@additive_terminal_object C Prod t Add) P (@one_cat_native_snake_alpha_diagram K C
  (@additive_preadditive C Prod t Add) C1 t (@additive_terminal_object C Prod t Add) T0 P A B X D b c h))
  (@kernel_adjunction_family_func K C (@additive_preadditive C Prod t Add) t (@additive_terminal_object C Prod t
  Add) P (@transf_arrow_diagram_func K C B X b)) (@one_cat_native_snake_kernel_first K C (@additive_preadditive
  C Prod t Add) C1 t (@additive_terminal_object C Prod t Add) T0 P Q A B X D b c h)
  (@one_cat_native_snake_six_term_result K C C1 Prod t Add T0 P Q N A B X D b c h)) (@finite_arrow_tail_arrow
  (Functor_cat K C) (@OneCatNativeExactArrowPair K C (@additive_preadditive C Prod t Add) C1 t
  (@additive_terminal_object C Prod t Add) T0 P Q N) (succ (succ (succ zero))) (@kernel_adjunction_family_func K
  C (@additive_preadditive C Prod t Add) t (@additive_terminal_object C Prod t Add) P
  (@one_cat_native_snake_alpha_diagram K C (@additive_preadditive C Prod t Add) C1 t (@additive_terminal_object
  C Prod t Add) T0 P A B X D b c h)) (@kernel_adjunction_family_func K C (@additive_preadditive C Prod t Add) t
  (@additive_terminal_object C Prod t Add) P (@transf_arrow_diagram_func K C B X b))
  (@one_cat_native_snake_kernel_first K C (@additive_preadditive C Prod t Add) C1 t (@additive_terminal_object C
  Prod t Add) T0 P Q A B X D b c h) (@one_cat_native_snake_six_term_result K C C1 Prod t Add T0 P Q N A B X D b
  c h)) (@finite_arrow_tail_rest (Functor_cat K C) (@OneCatNativeExactArrowPair K C (@additive_preadditive C
  Prod t Add) C1 t (@additive_terminal_object C Prod t Add) T0 P Q N) (succ (succ (succ zero)))
  (@kernel_adjunction_family_func K C (@additive_preadditive C Prod t Add) t (@additive_terminal_object C Prod t
  Add) P (@one_cat_native_snake_alpha_diagram K C (@additive_preadditive C Prod t Add) C1 t
  (@additive_terminal_object C Prod t Add) T0 P A B X D b c h)) (@kernel_adjunction_family_func K C
  (@additive_preadditive C Prod t Add) t (@additive_terminal_object C Prod t Add) P (@transf_arrow_diagram_func
  K C B X b)) (@one_cat_native_snake_kernel_first K C (@additive_preadditive C Prod t Add) C1 t
  (@additive_terminal_object C Prod t Add) T0 P Q A B X D b c h) (@one_cat_native_snake_six_term_result K C C1
  Prod t Add T0 P Q N A B X D b c h))) (@finite_arrow_tail_rest (Functor_cat K C) (@OneCatNativeExactArrowPair K
  C (@additive_preadditive C Prod t Add) C1 t (@additive_terminal_object C Prod t Add) T0 P Q N) (succ (succ
  zero)) (@kernel_adjunction_family_func K C (@additive_preadditive C Prod t Add) t (@additive_terminal_object C
  Prod t Add) P (@transf_arrow_diagram_func K C B X b)) (@finite_arrow_tail_next (Functor_cat K C)
  (@OneCatNativeExactArrowPair K C (@additive_preadditive C Prod t Add) C1 t (@additive_terminal_object C Prod t
  Add) T0 P Q N) (succ (succ (succ zero))) (@kernel_adjunction_family_func K C (@additive_preadditive C Prod t
  Add) t (@additive_terminal_object C Prod t Add) P (@one_cat_native_snake_alpha_diagram K C
  (@additive_preadditive C Prod t Add) C1 t (@additive_terminal_object C Prod t Add) T0 P A B X D b c h))
  (@kernel_adjunction_family_func K C (@additive_preadditive C Prod t Add) t (@additive_terminal_object C Prod t
  Add) P (@transf_arrow_diagram_func K C B X b)) (@one_cat_native_snake_kernel_first K C (@additive_preadditive
  C Prod t Add) C1 t (@additive_terminal_object C Prod t Add) T0 P Q A B X D b c h)
  (@one_cat_native_snake_six_term_result K C C1 Prod t Add T0 P Q N A B X D b c h)) (@finite_arrow_tail_arrow
  (Functor_cat K C) (@OneCatNativeExactArrowPair K C (@additive_preadditive C Prod t Add) C1 t
  (@additive_terminal_object C Prod t Add) T0 P Q N) (succ (succ (succ zero))) (@kernel_adjunction_family_func K
  C (@additive_preadditive C Prod t Add) t (@additive_terminal_object C Prod t Add) P
  (@one_cat_native_snake_alpha_diagram K C (@additive_preadditive C Prod t Add) C1 t (@additive_terminal_object
  C Prod t Add) T0 P A B X D b c h)) (@kernel_adjunction_family_func K C (@additive_preadditive C Prod t Add) t
  (@additive_terminal_object C Prod t Add) P (@transf_arrow_diagram_func K C B X b))
  (@one_cat_native_snake_kernel_first K C (@additive_preadditive C Prod t Add) C1 t (@additive_terminal_object C
  Prod t Add) T0 P Q A B X D b c h) (@one_cat_native_snake_six_term_result K C C1 Prod t Add T0 P Q N A B X D b
  c h)) (@finite_arrow_tail_rest (Functor_cat K C) (@OneCatNativeExactArrowPair K C (@additive_preadditive C
  Prod t Add) C1 t (@additive_terminal_object C Prod t Add) T0 P Q N) (succ (succ (succ zero)))
  (@kernel_adjunction_family_func K C (@additive_preadditive C Prod t Add) t (@additive_terminal_object C Prod t
  Add) P (@one_cat_native_snake_alpha_diagram K C (@additive_preadditive C Prod t Add) C1 t
  (@additive_terminal_object C Prod t Add) T0 P A B X D b c h)) (@kernel_adjunction_family_func K C
  (@additive_preadditive C Prod t Add) t (@additive_terminal_object C Prod t Add) P (@transf_arrow_diagram_func
  K C B X b)) (@one_cat_native_snake_kernel_first K C (@additive_preadditive C Prod t Add) C1 t
  (@additive_terminal_object C Prod t Add) T0 P Q A B X D b c h) (@one_cat_native_snake_six_term_result K C C1
  Prod t Add T0 P Q N A B X D b c h)))) (@finite_arrow_tail_rest (Functor_cat K C) (@OneCatNativeExactArrowPair
  K C (@additive_preadditive C Prod t Add) C1 t (@additive_terminal_object C Prod t Add) T0 P Q N) (succ zero)
  (@finite_arrow_tail_next (Functor_cat K C) (@OneCatNativeExactArrowPair K C (@additive_preadditive C Prod t
  Add) C1 t (@additive_terminal_object C Prod t Add) T0 P Q N) (succ (succ (succ zero)))
  (@kernel_adjunction_family_func K C (@additive_preadditive C Prod t Add) t (@additive_terminal_object C Prod t
  Add) P (@one_cat_native_snake_alpha_diagram K C (@additive_preadditive C Prod t Add) C1 t
  (@additive_terminal_object C Prod t Add) T0 P A B X D b c h)) (@kernel_adjunction_family_func K C
  (@additive_preadditive C Prod t Add) t (@additive_terminal_object C Prod t Add) P (@transf_arrow_diagram_func
  K C B X b)) (@one_cat_native_snake_kernel_first K C (@additive_preadditive C Prod t Add) C1 t
  (@additive_terminal_object C Prod t Add) T0 P Q A B X D b c h) (@one_cat_native_snake_six_term_result K C C1
  Prod t Add T0 P Q N A B X D b c h)) (@finite_arrow_tail_next (Functor_cat K C) (@OneCatNativeExactArrowPair K
  C (@additive_preadditive C Prod t Add) C1 t (@additive_terminal_object C Prod t Add) T0 P Q N) (succ (succ
  zero)) (@kernel_adjunction_family_func K C (@additive_preadditive C Prod t Add) t (@additive_terminal_object C
  Prod t Add) P (@transf_arrow_diagram_func K C B X b)) (@finite_arrow_tail_next (Functor_cat K C)
  (@OneCatNativeExactArrowPair K C (@additive_preadditive C Prod t Add) C1 t (@additive_terminal_object C Prod t
  Add) T0 P Q N) (succ (succ (succ zero))) (@kernel_adjunction_family_func K C (@additive_preadditive C Prod t
  Add) t (@additive_terminal_object C Prod t Add) P (@one_cat_native_snake_alpha_diagram K C
  (@additive_preadditive C Prod t Add) C1 t (@additive_terminal_object C Prod t Add) T0 P A B X D b c h))
  (@kernel_adjunction_family_func K C (@additive_preadditive C Prod t Add) t (@additive_terminal_object C Prod t
  Add) P (@transf_arrow_diagram_func K C B X b)) (@one_cat_native_snake_kernel_first K C (@additive_preadditive
  C Prod t Add) C1 t (@additive_terminal_object C Prod t Add) T0 P Q A B X D b c h)
  (@one_cat_native_snake_six_term_result K C C1 Prod t Add T0 P Q N A B X D b c h)) (@finite_arrow_tail_arrow
  (Functor_cat K C) (@OneCatNativeExactArrowPair K C (@additive_preadditive C Prod t Add) C1 t
  (@additive_terminal_object C Prod t Add) T0 P Q N) (succ (succ (succ zero))) (@kernel_adjunction_family_func K
  C (@additive_preadditive C Prod t Add) t (@additive_terminal_object C Prod t Add) P
  (@one_cat_native_snake_alpha_diagram K C (@additive_preadditive C Prod t Add) C1 t (@additive_terminal_object
  C Prod t Add) T0 P A B X D b c h)) (@kernel_adjunction_family_func K C (@additive_preadditive C Prod t Add) t
  (@additive_terminal_object C Prod t Add) P (@transf_arrow_diagram_func K C B X b))
  (@one_cat_native_snake_kernel_first K C (@additive_preadditive C Prod t Add) C1 t (@additive_terminal_object C
  Prod t Add) T0 P Q A B X D b c h) (@one_cat_native_snake_six_term_result K C C1 Prod t Add T0 P Q N A B X D b
  c h)) (@finite_arrow_tail_rest (Functor_cat K C) (@OneCatNativeExactArrowPair K C (@additive_preadditive C
  Prod t Add) C1 t (@additive_terminal_object C Prod t Add) T0 P Q N) (succ (succ (succ zero)))
  (@kernel_adjunction_family_func K C (@additive_preadditive C Prod t Add) t (@additive_terminal_object C Prod t
  Add) P (@one_cat_native_snake_alpha_diagram K C (@additive_preadditive C Prod t Add) C1 t
  (@additive_terminal_object C Prod t Add) T0 P A B X D b c h)) (@kernel_adjunction_family_func K C
  (@additive_preadditive C Prod t Add) t (@additive_terminal_object C Prod t Add) P (@transf_arrow_diagram_func
  K C B X b)) (@one_cat_native_snake_kernel_first K C (@additive_preadditive C Prod t Add) C1 t
  (@additive_terminal_object C Prod t Add) T0 P Q A B X D b c h) (@one_cat_native_snake_six_term_result K C C1
  Prod t Add T0 P Q N A B X D b c h))) (@finite_arrow_tail_arrow (Functor_cat K C) (@OneCatNativeExactArrowPair
  K C (@additive_preadditive C Prod t Add) C1 t (@additive_terminal_object C Prod t Add) T0 P Q N) (succ (succ
  zero)) (@kernel_adjunction_family_func K C (@additive_preadditive C Prod t Add) t (@additive_terminal_object C
  Prod t Add) P (@transf_arrow_diagram_func K C B X b)) (@finite_arrow_tail_next (Functor_cat K C)
  (@OneCatNativeExactArrowPair K C (@additive_preadditive C Prod t Add) C1 t (@additive_terminal_object C Prod t
  Add) T0 P Q N) (succ (succ (succ zero))) (@kernel_adjunction_family_func K C (@additive_preadditive C Prod t
  Add) t (@additive_terminal_object C Prod t Add) P (@one_cat_native_snake_alpha_diagram K C
  (@additive_preadditive C Prod t Add) C1 t (@additive_terminal_object C Prod t Add) T0 P A B X D b c h))
  (@kernel_adjunction_family_func K C (@additive_preadditive C Prod t Add) t (@additive_terminal_object C Prod t
  Add) P (@transf_arrow_diagram_func K C B X b)) (@one_cat_native_snake_kernel_first K C (@additive_preadditive
  C Prod t Add) C1 t (@additive_terminal_object C Prod t Add) T0 P Q A B X D b c h)
  (@one_cat_native_snake_six_term_result K C C1 Prod t Add T0 P Q N A B X D b c h)) (@finite_arrow_tail_arrow
  (Functor_cat K C) (@OneCatNativeExactArrowPair K C (@additive_preadditive C Prod t Add) C1 t
  (@additive_terminal_object C Prod t Add) T0 P Q N) (succ (succ (succ zero))) (@kernel_adjunction_family_func K
  C (@additive_preadditive C Prod t Add) t (@additive_terminal_object C Prod t Add) P
  (@one_cat_native_snake_alpha_diagram K C (@additive_preadditive C Prod t Add) C1 t (@additive_terminal_object
  C Prod t Add) T0 P A B X D b c h)) (@kernel_adjunction_family_func K C (@additive_preadditive C Prod t Add) t
  (@additive_terminal_object C Prod t Add) P (@transf_arrow_diagram_func K C B X b))
  (@one_cat_native_snake_kernel_first K C (@additive_preadditive C Prod t Add) C1 t (@additive_terminal_object C
  Prod t Add) T0 P Q A B X D b c h) (@one_cat_native_snake_six_term_result K C C1 Prod t Add T0 P Q N A B X D b
  c h)) (@finite_arrow_tail_rest (Functor_cat K C) (@OneCatNativeExactArrowPair K C (@additive_preadditive C
  Prod t Add) C1 t (@additive_terminal_object C Prod t Add) T0 P Q N) (succ (succ (succ zero)))
  (@kernel_adjunction_family_func K C (@additive_preadditive C Prod t Add) t (@additive_terminal_object C Prod t
  Add) P (@one_cat_native_snake_alpha_diagram K C (@additive_preadditive C Prod t Add) C1 t
  (@additive_terminal_object C Prod t Add) T0 P A B X D b c h)) (@kernel_adjunction_family_func K C
  (@additive_preadditive C Prod t Add) t (@additive_terminal_object C Prod t Add) P (@transf_arrow_diagram_func
  K C B X b)) (@one_cat_native_snake_kernel_first K C (@additive_preadditive C Prod t Add) C1 t
  (@additive_terminal_object C Prod t Add) T0 P Q A B X D b c h) (@one_cat_native_snake_six_term_result K C C1
  Prod t Add T0 P Q N A B X D b c h))) (@finite_arrow_tail_rest (Functor_cat K C) (@OneCatNativeExactArrowPair K
  C (@additive_preadditive C Prod t Add) C1 t (@additive_terminal_object C Prod t Add) T0 P Q N) (succ (succ
  zero)) (@kernel_adjunction_family_func K C (@additive_preadditive C Prod t Add) t (@additive_terminal_object C
  Prod t Add) P (@transf_arrow_diagram_func K C B X b)) (@finite_arrow_tail_next (Functor_cat K C)
  (@OneCatNativeExactArrowPair K C (@additive_preadditive C Prod t Add) C1 t (@additive_terminal_object C Prod t
  Add) T0 P Q N) (succ (succ (succ zero))) (@kernel_adjunction_family_func K C (@additive_preadditive C Prod t
  Add) t (@additive_terminal_object C Prod t Add) P (@one_cat_native_snake_alpha_diagram K C
  (@additive_preadditive C Prod t Add) C1 t (@additive_terminal_object C Prod t Add) T0 P A B X D b c h))
  (@kernel_adjunction_family_func K C (@additive_preadditive C Prod t Add) t (@additive_terminal_object C Prod t
  Add) P (@transf_arrow_diagram_func K C B X b)) (@one_cat_native_snake_kernel_first K C (@additive_preadditive
  C Prod t Add) C1 t (@additive_terminal_object C Prod t Add) T0 P Q A B X D b c h)
  (@one_cat_native_snake_six_term_result K C C1 Prod t Add T0 P Q N A B X D b c h)) (@finite_arrow_tail_arrow
  (Functor_cat K C) (@OneCatNativeExactArrowPair K C (@additive_preadditive C Prod t Add) C1 t
  (@additive_terminal_object C Prod t Add) T0 P Q N) (succ (succ (succ zero))) (@kernel_adjunction_family_func K
  C (@additive_preadditive C Prod t Add) t (@additive_terminal_object C Prod t Add) P
  (@one_cat_native_snake_alpha_diagram K C (@additive_preadditive C Prod t Add) C1 t (@additive_terminal_object
  C Prod t Add) T0 P A B X D b c h)) (@kernel_adjunction_family_func K C (@additive_preadditive C Prod t Add) t
  (@additive_terminal_object C Prod t Add) P (@transf_arrow_diagram_func K C B X b))
  (@one_cat_native_snake_kernel_first K C (@additive_preadditive C Prod t Add) C1 t (@additive_terminal_object C
  Prod t Add) T0 P Q A B X D b c h) (@one_cat_native_snake_six_term_result K C C1 Prod t Add T0 P Q N A B X D b
  c h)) (@finite_arrow_tail_rest (Functor_cat K C) (@OneCatNativeExactArrowPair K C (@additive_preadditive C
  Prod t Add) C1 t (@additive_terminal_object C Prod t Add) T0 P Q N) (succ (succ (succ zero)))
  (@kernel_adjunction_family_func K C (@additive_preadditive C Prod t Add) t (@additive_terminal_object C Prod t
  Add) P (@one_cat_native_snake_alpha_diagram K C (@additive_preadditive C Prod t Add) C1 t
  (@additive_terminal_object C Prod t Add) T0 P A B X D b c h)) (@kernel_adjunction_family_func K C
  (@additive_preadditive C Prod t Add) t (@additive_terminal_object C Prod t Add) P (@transf_arrow_diagram_func
  K C B X b)) (@one_cat_native_snake_kernel_first K C (@additive_preadditive C Prod t Add) C1 t
  (@additive_terminal_object C Prod t Add) T0 P Q A B X D b c h) (@one_cat_native_snake_six_term_result K C C1
  Prod t Add T0 P Q N A B X D b c h))))) (@finite_arrow_tail_arrow (Functor_cat K C)
  (@OneCatNativeExactArrowPair K C (@additive_preadditive C Prod t Add) C1 t (@additive_terminal_object C Prod t
  Add) T0 P Q N) (succ zero) (@finite_arrow_tail_next (Functor_cat K C) (@OneCatNativeExactArrowPair K C
  (@additive_preadditive C Prod t Add) C1 t (@additive_terminal_object C Prod t Add) T0 P Q N) (succ (succ (succ
  zero))) (@kernel_adjunction_family_func K C (@additive_preadditive C Prod t Add) t (@additive_terminal_object
  C Prod t Add) P (@one_cat_native_snake_alpha_diagram K C (@additive_preadditive C Prod t Add) C1 t
  (@additive_terminal_object C Prod t Add) T0 P A B X D b c h)) (@kernel_adjunction_family_func K C
  (@additive_preadditive C Prod t Add) t (@additive_terminal_object C Prod t Add) P (@transf_arrow_diagram_func
  K C B X b)) (@one_cat_native_snake_kernel_first K C (@additive_preadditive C Prod t Add) C1 t
  (@additive_terminal_object C Prod t Add) T0 P Q A B X D b c h) (@one_cat_native_snake_six_term_result K C C1
  Prod t Add T0 P Q N A B X D b c h)) (@finite_arrow_tail_next (Functor_cat K C) (@OneCatNativeExactArrowPair K
  C (@additive_preadditive C Prod t Add) C1 t (@additive_terminal_object C Prod t Add) T0 P Q N) (succ (succ
  zero)) (@kernel_adjunction_family_func K C (@additive_preadditive C Prod t Add) t (@additive_terminal_object C
  Prod t Add) P (@transf_arrow_diagram_func K C B X b)) (@finite_arrow_tail_next (Functor_cat K C)
  (@OneCatNativeExactArrowPair K C (@additive_preadditive C Prod t Add) C1 t (@additive_terminal_object C Prod t
  Add) T0 P Q N) (succ (succ (succ zero))) (@kernel_adjunction_family_func K C (@additive_preadditive C Prod t
  Add) t (@additive_terminal_object C Prod t Add) P (@one_cat_native_snake_alpha_diagram K C
  (@additive_preadditive C Prod t Add) C1 t (@additive_terminal_object C Prod t Add) T0 P A B X D b c h))
  (@kernel_adjunction_family_func K C (@additive_preadditive C Prod t Add) t (@additive_terminal_object C Prod t
  Add) P (@transf_arrow_diagram_func K C B X b)) (@one_cat_native_snake_kernel_first K C (@additive_preadditive
  C Prod t Add) C1 t (@additive_terminal_object C Prod t Add) T0 P Q A B X D b c h)
  (@one_cat_native_snake_six_term_result K C C1 Prod t Add T0 P Q N A B X D b c h)) (@finite_arrow_tail_arrow
  (Functor_cat K C) (@OneCatNativeExactArrowPair K C (@additive_preadditive C Prod t Add) C1 t
  (@additive_terminal_object C Prod t Add) T0 P Q N) (succ (succ (succ zero))) (@kernel_adjunction_family_func K
  C (@additive_preadditive C Prod t Add) t (@additive_terminal_object C Prod t Add) P
  (@one_cat_native_snake_alpha_diagram K C (@additive_preadditive C Prod t Add) C1 t (@additive_terminal_object
  C Prod t Add) T0 P A B X D b c h)) (@kernel_adjunction_family_func K C (@additive_preadditive C Prod t Add) t
  (@additive_terminal_object C Prod t Add) P (@transf_arrow_diagram_func K C B X b))
  (@one_cat_native_snake_kernel_first K C (@additive_preadditive C Prod t Add) C1 t (@additive_terminal_object C
  Prod t Add) T0 P Q A B X D b c h) (@one_cat_native_snake_six_term_result K C C1 Prod t Add T0 P Q N A B X D b
  c h)) (@finite_arrow_tail_rest (Functor_cat K C) (@OneCatNativeExactArrowPair K C (@additive_preadditive C
  Prod t Add) C1 t (@additive_terminal_object C Prod t Add) T0 P Q N) (succ (succ (succ zero)))
  (@kernel_adjunction_family_func K C (@additive_preadditive C Prod t Add) t (@additive_terminal_object C Prod t
  Add) P (@one_cat_native_snake_alpha_diagram K C (@additive_preadditive C Prod t Add) C1 t
  (@additive_terminal_object C Prod t Add) T0 P A B X D b c h)) (@kernel_adjunction_family_func K C
  (@additive_preadditive C Prod t Add) t (@additive_terminal_object C Prod t Add) P (@transf_arrow_diagram_func
  K C B X b)) (@one_cat_native_snake_kernel_first K C (@additive_preadditive C Prod t Add) C1 t
  (@additive_terminal_object C Prod t Add) T0 P Q A B X D b c h) (@one_cat_native_snake_six_term_result K C C1
  Prod t Add T0 P Q N A B X D b c h))) (@finite_arrow_tail_arrow (Functor_cat K C) (@OneCatNativeExactArrowPair
  K C (@additive_preadditive C Prod t Add) C1 t (@additive_terminal_object C Prod t Add) T0 P Q N) (succ (succ
  zero)) (@kernel_adjunction_family_func K C (@additive_preadditive C Prod t Add) t (@additive_terminal_object C
  Prod t Add) P (@transf_arrow_diagram_func K C B X b)) (@finite_arrow_tail_next (Functor_cat K C)
  (@OneCatNativeExactArrowPair K C (@additive_preadditive C Prod t Add) C1 t (@additive_terminal_object C Prod t
  Add) T0 P Q N) (succ (succ (succ zero))) (@kernel_adjunction_family_func K C (@additive_preadditive C Prod t
  Add) t (@additive_terminal_object C Prod t Add) P (@one_cat_native_snake_alpha_diagram K C
  (@additive_preadditive C Prod t Add) C1 t (@additive_terminal_object C Prod t Add) T0 P A B X D b c h))
  (@kernel_adjunction_family_func K C (@additive_preadditive C Prod t Add) t (@additive_terminal_object C Prod t
  Add) P (@transf_arrow_diagram_func K C B X b)) (@one_cat_native_snake_kernel_first K C (@additive_preadditive
  C Prod t Add) C1 t (@additive_terminal_object C Prod t Add) T0 P Q A B X D b c h)
  (@one_cat_native_snake_six_term_result K C C1 Prod t Add T0 P Q N A B X D b c h)) (@finite_arrow_tail_arrow
  (Functor_cat K C) (@OneCatNativeExactArrowPair K C (@additive_preadditive C Prod t Add) C1 t
  (@additive_terminal_object C Prod t Add) T0 P Q N) (succ (succ (succ zero))) (@kernel_adjunction_family_func K
  C (@additive_preadditive C Prod t Add) t (@additive_terminal_object C Prod t Add) P
  (@one_cat_native_snake_alpha_diagram K C (@additive_preadditive C Prod t Add) C1 t (@additive_terminal_object
  C Prod t Add) T0 P A B X D b c h)) (@kernel_adjunction_family_func K C (@additive_preadditive C Prod t Add) t
  (@additive_terminal_object C Prod t Add) P (@transf_arrow_diagram_func K C B X b))
  (@one_cat_native_snake_kernel_first K C (@additive_preadditive C Prod t Add) C1 t (@additive_terminal_object C
  Prod t Add) T0 P Q A B X D b c h) (@one_cat_native_snake_six_term_result K C C1 Prod t Add T0 P Q N A B X D b
  c h)) (@finite_arrow_tail_rest (Functor_cat K C) (@OneCatNativeExactArrowPair K C (@additive_preadditive C
  Prod t Add) C1 t (@additive_terminal_object C Prod t Add) T0 P Q N) (succ (succ (succ zero)))
  (@kernel_adjunction_family_func K C (@additive_preadditive C Prod t Add) t (@additive_terminal_object C Prod t
  Add) P (@one_cat_native_snake_alpha_diagram K C (@additive_preadditive C Prod t Add) C1 t
  (@additive_terminal_object C Prod t Add) T0 P A B X D b c h)) (@kernel_adjunction_family_func K C
  (@additive_preadditive C Prod t Add) t (@additive_terminal_object C Prod t Add) P (@transf_arrow_diagram_func
  K C B X b)) (@one_cat_native_snake_kernel_first K C (@additive_preadditive C Prod t Add) C1 t
  (@additive_terminal_object C Prod t Add) T0 P Q A B X D b c h) (@one_cat_native_snake_six_term_result K C C1
  Prod t Add T0 P Q N A B X D b c h))) (@finite_arrow_tail_rest (Functor_cat K C) (@OneCatNativeExactArrowPair K
  C (@additive_preadditive C Prod t Add) C1 t (@additive_terminal_object C Prod t Add) T0 P Q N) (succ (succ
  zero)) (@kernel_adjunction_family_func K C (@additive_preadditive C Prod t Add) t (@additive_terminal_object C
  Prod t Add) P (@transf_arrow_diagram_func K C B X b)) (@finite_arrow_tail_next (Functor_cat K C)
  (@OneCatNativeExactArrowPair K C (@additive_preadditive C Prod t Add) C1 t (@additive_terminal_object C Prod t
  Add) T0 P Q N) (succ (succ (succ zero))) (@kernel_adjunction_family_func K C (@additive_preadditive C Prod t
  Add) t (@additive_terminal_object C Prod t Add) P (@one_cat_native_snake_alpha_diagram K C
  (@additive_preadditive C Prod t Add) C1 t (@additive_terminal_object C Prod t Add) T0 P A B X D b c h))
  (@kernel_adjunction_family_func K C (@additive_preadditive C Prod t Add) t (@additive_terminal_object C Prod t
  Add) P (@transf_arrow_diagram_func K C B X b)) (@one_cat_native_snake_kernel_first K C (@additive_preadditive
  C Prod t Add) C1 t (@additive_terminal_object C Prod t Add) T0 P Q A B X D b c h)
  (@one_cat_native_snake_six_term_result K C C1 Prod t Add T0 P Q N A B X D b c h)) (@finite_arrow_tail_arrow
  (Functor_cat K C) (@OneCatNativeExactArrowPair K C (@additive_preadditive C Prod t Add) C1 t
  (@additive_terminal_object C Prod t Add) T0 P Q N) (succ (succ (succ zero))) (@kernel_adjunction_family_func K
  C (@additive_preadditive C Prod t Add) t (@additive_terminal_object C Prod t Add) P
  (@one_cat_native_snake_alpha_diagram K C (@additive_preadditive C Prod t Add) C1 t (@additive_terminal_object
  C Prod t Add) T0 P A B X D b c h)) (@kernel_adjunction_family_func K C (@additive_preadditive C Prod t Add) t
  (@additive_terminal_object C Prod t Add) P (@transf_arrow_diagram_func K C B X b))
  (@one_cat_native_snake_kernel_first K C (@additive_preadditive C Prod t Add) C1 t (@additive_terminal_object C
  Prod t Add) T0 P Q A B X D b c h) (@one_cat_native_snake_six_term_result K C C1 Prod t Add T0 P Q N A B X D b
  c h)) (@finite_arrow_tail_rest (Functor_cat K C) (@OneCatNativeExactArrowPair K C (@additive_preadditive C
  Prod t Add) C1 t (@additive_terminal_object C Prod t Add) T0 P Q N) (succ (succ (succ zero)))
  (@kernel_adjunction_family_func K C (@additive_preadditive C Prod t Add) t (@additive_terminal_object C Prod t
  Add) P (@one_cat_native_snake_alpha_diagram K C (@additive_preadditive C Prod t Add) C1 t
  (@additive_terminal_object C Prod t Add) T0 P A B X D b c h)) (@kernel_adjunction_family_func K C
  (@additive_preadditive C Prod t Add) t (@additive_terminal_object C Prod t Add) P (@transf_arrow_diagram_func
  K C B X b)) (@one_cat_native_snake_kernel_first K C (@additive_preadditive C Prod t Add) C1 t
  (@additive_terminal_object C Prod t Add) T0 P Q A B X D b c h) (@one_cat_native_snake_six_term_result K C C1
  Prod t Add T0 P Q N A B X D b c h)))) (@finite_arrow_tail_arrow (Functor_cat K C) (@OneCatNativeExactArrowPair
  K C (@additive_preadditive C Prod t Add) C1 t (@additive_terminal_object C Prod t Add) T0 P Q N) zero
  (@finite_arrow_tail_next (Functor_cat K C) (@OneCatNativeExactArrowPair K C (@additive_preadditive C Prod t
  Add) C1 t (@additive_terminal_object C Prod t Add) T0 P Q N) (succ (succ zero))
  (@kernel_adjunction_family_func K C (@additive_preadditive C Prod t Add) t (@additive_terminal_object C Prod t
  Add) P (@transf_arrow_diagram_func K C B X b)) (@finite_arrow_tail_next (Functor_cat K C)
  (@OneCatNativeExactArrowPair K C (@additive_preadditive C Prod t Add) C1 t (@additive_terminal_object C Prod t
  Add) T0 P Q N) (succ (succ (succ zero))) (@kernel_adjunction_family_func K C (@additive_preadditive C Prod t
  Add) t (@additive_terminal_object C Prod t Add) P (@one_cat_native_snake_alpha_diagram K C
  (@additive_preadditive C Prod t Add) C1 t (@additive_terminal_object C Prod t Add) T0 P A B X D b c h))
  (@kernel_adjunction_family_func K C (@additive_preadditive C Prod t Add) t (@additive_terminal_object C Prod t
  Add) P (@transf_arrow_diagram_func K C B X b)) (@one_cat_native_snake_kernel_first K C (@additive_preadditive
  C Prod t Add) C1 t (@additive_terminal_object C Prod t Add) T0 P Q A B X D b c h)
  (@one_cat_native_snake_six_term_result K C C1 Prod t Add T0 P Q N A B X D b c h)) (@finite_arrow_tail_arrow
  (Functor_cat K C) (@OneCatNativeExactArrowPair K C (@additive_preadditive C Prod t Add) C1 t
  (@additive_terminal_object C Prod t Add) T0 P Q N) (succ (succ (succ zero))) (@kernel_adjunction_family_func K
  C (@additive_preadditive C Prod t Add) t (@additive_terminal_object C Prod t Add) P
  (@one_cat_native_snake_alpha_diagram K C (@additive_preadditive C Prod t Add) C1 t (@additive_terminal_object
  C Prod t Add) T0 P A B X D b c h)) (@kernel_adjunction_family_func K C (@additive_preadditive C Prod t Add) t
  (@additive_terminal_object C Prod t Add) P (@transf_arrow_diagram_func K C B X b))
  (@one_cat_native_snake_kernel_first K C (@additive_preadditive C Prod t Add) C1 t (@additive_terminal_object C
  Prod t Add) T0 P Q A B X D b c h) (@one_cat_native_snake_six_term_result K C C1 Prod t Add T0 P Q N A B X D b
  c h)) (@finite_arrow_tail_rest (Functor_cat K C) (@OneCatNativeExactArrowPair K C (@additive_preadditive C
  Prod t Add) C1 t (@additive_terminal_object C Prod t Add) T0 P Q N) (succ (succ (succ zero)))
  (@kernel_adjunction_family_func K C (@additive_preadditive C Prod t Add) t (@additive_terminal_object C Prod t
  Add) P (@one_cat_native_snake_alpha_diagram K C (@additive_preadditive C Prod t Add) C1 t
  (@additive_terminal_object C Prod t Add) T0 P A B X D b c h)) (@kernel_adjunction_family_func K C
  (@additive_preadditive C Prod t Add) t (@additive_terminal_object C Prod t Add) P (@transf_arrow_diagram_func
  K C B X b)) (@one_cat_native_snake_kernel_first K C (@additive_preadditive C Prod t Add) C1 t
  (@additive_terminal_object C Prod t Add) T0 P Q A B X D b c h) (@one_cat_native_snake_six_term_result K C C1
  Prod t Add T0 P Q N A B X D b c h))) (@finite_arrow_tail_next (Functor_cat K C) (@OneCatNativeExactArrowPair K
  C (@additive_preadditive C Prod t Add) C1 t (@additive_terminal_object C Prod t Add) T0 P Q N) (succ zero)
  (@finite_arrow_tail_next (Functor_cat K C) (@OneCatNativeExactArrowPair K C (@additive_preadditive C Prod t
  Add) C1 t (@additive_terminal_object C Prod t Add) T0 P Q N) (succ (succ (succ zero)))
  (@kernel_adjunction_family_func K C (@additive_preadditive C Prod t Add) t (@additive_terminal_object C Prod t
  Add) P (@one_cat_native_snake_alpha_diagram K C (@additive_preadditive C Prod t Add) C1 t
  (@additive_terminal_object C Prod t Add) T0 P A B X D b c h)) (@kernel_adjunction_family_func K C
  (@additive_preadditive C Prod t Add) t (@additive_terminal_object C Prod t Add) P (@transf_arrow_diagram_func
  K C B X b)) (@one_cat_native_snake_kernel_first K C (@additive_preadditive C Prod t Add) C1 t
  (@additive_terminal_object C Prod t Add) T0 P Q A B X D b c h) (@one_cat_native_snake_six_term_result K C C1
  Prod t Add T0 P Q N A B X D b c h)) (@finite_arrow_tail_next (Functor_cat K C) (@OneCatNativeExactArrowPair K
  C (@additive_preadditive C Prod t Add) C1 t (@additive_terminal_object C Prod t Add) T0 P Q N) (succ (succ
  zero)) (@kernel_adjunction_family_func K C (@additive_preadditive C Prod t Add) t (@additive_terminal_object C
  Prod t Add) P (@transf_arrow_diagram_func K C B X b)) (@finite_arrow_tail_next (Functor_cat K C)
  (@OneCatNativeExactArrowPair K C (@additive_preadditive C Prod t Add) C1 t (@additive_terminal_object C Prod t
  Add) T0 P Q N) (succ (succ (succ zero))) (@kernel_adjunction_family_func K C (@additive_preadditive C Prod t
  Add) t (@additive_terminal_object C Prod t Add) P (@one_cat_native_snake_alpha_diagram K C
  (@additive_preadditive C Prod t Add) C1 t (@additive_terminal_object C Prod t Add) T0 P A B X D b c h))
  (@kernel_adjunction_family_func K C (@additive_preadditive C Prod t Add) t (@additive_terminal_object C Prod t
  Add) P (@transf_arrow_diagram_func K C B X b)) (@one_cat_native_snake_kernel_first K C (@additive_preadditive
  C Prod t Add) C1 t (@additive_terminal_object C Prod t Add) T0 P Q A B X D b c h)
  (@one_cat_native_snake_six_term_result K C C1 Prod t Add T0 P Q N A B X D b c h)) (@finite_arrow_tail_arrow
  (Functor_cat K C) (@OneCatNativeExactArrowPair K C (@additive_preadditive C Prod t Add) C1 t
  (@additive_terminal_object C Prod t Add) T0 P Q N) (succ (succ (succ zero))) (@kernel_adjunction_family_func K
  C (@additive_preadditive C Prod t Add) t (@additive_terminal_object C Prod t Add) P
  (@one_cat_native_snake_alpha_diagram K C (@additive_preadditive C Prod t Add) C1 t (@additive_terminal_object
  C Prod t Add) T0 P A B X D b c h)) (@kernel_adjunction_family_func K C (@additive_preadditive C Prod t Add) t
  (@additive_terminal_object C Prod t Add) P (@transf_arrow_diagram_func K C B X b))
  (@one_cat_native_snake_kernel_first K C (@additive_preadditive C Prod t Add) C1 t (@additive_terminal_object C
  Prod t Add) T0 P Q A B X D b c h) (@one_cat_native_snake_six_term_result K C C1 Prod t Add T0 P Q N A B X D b
  c h)) (@finite_arrow_tail_rest (Functor_cat K C) (@OneCatNativeExactArrowPair K C (@additive_preadditive C
  Prod t Add) C1 t (@additive_terminal_object C Prod t Add) T0 P Q N) (succ (succ (succ zero)))
  (@kernel_adjunction_family_func K C (@additive_preadditive C Prod t Add) t (@additive_terminal_object C Prod t
  Add) P (@one_cat_native_snake_alpha_diagram K C (@additive_preadditive C Prod t Add) C1 t
  (@additive_terminal_object C Prod t Add) T0 P A B X D b c h)) (@kernel_adjunction_family_func K C
  (@additive_preadditive C Prod t Add) t (@additive_terminal_object C Prod t Add) P (@transf_arrow_diagram_func
  K C B X b)) (@one_cat_native_snake_kernel_first K C (@additive_preadditive C Prod t Add) C1 t
  (@additive_terminal_object C Prod t Add) T0 P Q A B X D b c h) (@one_cat_native_snake_six_term_result K C C1
  Prod t Add T0 P Q N A B X D b c h))) (@finite_arrow_tail_arrow (Functor_cat K C) (@OneCatNativeExactArrowPair
  K C (@additive_preadditive C Prod t Add) C1 t (@additive_terminal_object C Prod t Add) T0 P Q N) (succ (succ
  zero)) (@kernel_adjunction_family_func K C (@additive_preadditive C Prod t Add) t (@additive_terminal_object C
  Prod t Add) P (@transf_arrow_diagram_func K C B X b)) (@finite_arrow_tail_next (Functor_cat K C)
  (@OneCatNativeExactArrowPair K C (@additive_preadditive C Prod t Add) C1 t (@additive_terminal_object C Prod t
  Add) T0 P Q N) (succ (succ (succ zero))) (@kernel_adjunction_family_func K C (@additive_preadditive C Prod t
  Add) t (@additive_terminal_object C Prod t Add) P (@one_cat_native_snake_alpha_diagram K C
  (@additive_preadditive C Prod t Add) C1 t (@additive_terminal_object C Prod t Add) T0 P A B X D b c h))
  (@kernel_adjunction_family_func K C (@additive_preadditive C Prod t Add) t (@additive_terminal_object C Prod t
  Add) P (@transf_arrow_diagram_func K C B X b)) (@one_cat_native_snake_kernel_first K C (@additive_preadditive
  C Prod t Add) C1 t (@additive_terminal_object C Prod t Add) T0 P Q A B X D b c h)
  (@one_cat_native_snake_six_term_result K C C1 Prod t Add T0 P Q N A B X D b c h)) (@finite_arrow_tail_arrow
  (Functor_cat K C) (@OneCatNativeExactArrowPair K C (@additive_preadditive C Prod t Add) C1 t
  (@additive_terminal_object C Prod t Add) T0 P Q N) (succ (succ (succ zero))) (@kernel_adjunction_family_func K
  C (@additive_preadditive C Prod t Add) t (@additive_terminal_object C Prod t Add) P
  (@one_cat_native_snake_alpha_diagram K C (@additive_preadditive C Prod t Add) C1 t (@additive_terminal_object
  C Prod t Add) T0 P A B X D b c h)) (@kernel_adjunction_family_func K C (@additive_preadditive C Prod t Add) t
  (@additive_terminal_object C Prod t Add) P (@transf_arrow_diagram_func K C B X b))
  (@one_cat_native_snake_kernel_first K C (@additive_preadditive C Prod t Add) C1 t (@additive_terminal_object C
  Prod t Add) T0 P Q A B X D b c h) (@one_cat_native_snake_six_term_result K C C1 Prod t Add T0 P Q N A B X D b
  c h)) (@finite_arrow_tail_rest (Functor_cat K C) (@OneCatNativeExactArrowPair K C (@additive_preadditive C
  Prod t Add) C1 t (@additive_terminal_object C Prod t Add) T0 P Q N) (succ (succ (succ zero)))
  (@kernel_adjunction_family_func K C (@additive_preadditive C Prod t Add) t (@additive_terminal_object C Prod t
  Add) P (@one_cat_native_snake_alpha_diagram K C (@additive_preadditive C Prod t Add) C1 t
  (@additive_terminal_object C Prod t Add) T0 P A B X D b c h)) (@kernel_adjunction_family_func K C
  (@additive_preadditive C Prod t Add) t (@additive_terminal_object C Prod t Add) P (@transf_arrow_diagram_func
  K C B X b)) (@one_cat_native_snake_kernel_first K C (@additive_preadditive C Prod t Add) C1 t
  (@additive_terminal_object C Prod t Add) T0 P Q A B X D b c h) (@one_cat_native_snake_six_term_result K C C1
  Prod t Add T0 P Q N A B X D b c h))) (@finite_arrow_tail_rest (Functor_cat K C) (@OneCatNativeExactArrowPair K
  C (@additive_preadditive C Prod t Add) C1 t (@additive_terminal_object C Prod t Add) T0 P Q N) (succ (succ
  zero)) (@kernel_adjunction_family_func K C (@additive_preadditive C Prod t Add) t (@additive_terminal_object C
  Prod t Add) P (@transf_arrow_diagram_func K C B X b)) (@finite_arrow_tail_next (Functor_cat K C)
  (@OneCatNativeExactArrowPair K C (@additive_preadditive C Prod t Add) C1 t (@additive_terminal_object C Prod t
  Add) T0 P Q N) (succ (succ (succ zero))) (@kernel_adjunction_family_func K C (@additive_preadditive C Prod t
  Add) t (@additive_terminal_object C Prod t Add) P (@one_cat_native_snake_alpha_diagram K C
  (@additive_preadditive C Prod t Add) C1 t (@additive_terminal_object C Prod t Add) T0 P A B X D b c h))
  (@kernel_adjunction_family_func K C (@additive_preadditive C Prod t Add) t (@additive_terminal_object C Prod t
  Add) P (@transf_arrow_diagram_func K C B X b)) (@one_cat_native_snake_kernel_first K C (@additive_preadditive
  C Prod t Add) C1 t (@additive_terminal_object C Prod t Add) T0 P Q A B X D b c h)
  (@one_cat_native_snake_six_term_result K C C1 Prod t Add T0 P Q N A B X D b c h)) (@finite_arrow_tail_arrow
  (Functor_cat K C) (@OneCatNativeExactArrowPair K C (@additive_preadditive C Prod t Add) C1 t
  (@additive_terminal_object C Prod t Add) T0 P Q N) (succ (succ (succ zero))) (@kernel_adjunction_family_func K
  C (@additive_preadditive C Prod t Add) t (@additive_terminal_object C Prod t Add) P
  (@one_cat_native_snake_alpha_diagram K C (@additive_preadditive C Prod t Add) C1 t (@additive_terminal_object
  C Prod t Add) T0 P A B X D b c h)) (@kernel_adjunction_family_func K C (@additive_preadditive C Prod t Add) t
  (@additive_terminal_object C Prod t Add) P (@transf_arrow_diagram_func K C B X b))
  (@one_cat_native_snake_kernel_first K C (@additive_preadditive C Prod t Add) C1 t (@additive_terminal_object C
  Prod t Add) T0 P Q A B X D b c h) (@one_cat_native_snake_six_term_result K C C1 Prod t Add T0 P Q N A B X D b
  c h)) (@finite_arrow_tail_rest (Functor_cat K C) (@OneCatNativeExactArrowPair K C (@additive_preadditive C
  Prod t Add) C1 t (@additive_terminal_object C Prod t Add) T0 P Q N) (succ (succ (succ zero)))
  (@kernel_adjunction_family_func K C (@additive_preadditive C Prod t Add) t (@additive_terminal_object C Prod t
  Add) P (@one_cat_native_snake_alpha_diagram K C (@additive_preadditive C Prod t Add) C1 t
  (@additive_terminal_object C Prod t Add) T0 P A B X D b c h)) (@kernel_adjunction_family_func K C
  (@additive_preadditive C Prod t Add) t (@additive_terminal_object C Prod t Add) P (@transf_arrow_diagram_func
  K C B X b)) (@one_cat_native_snake_kernel_first K C (@additive_preadditive C Prod t Add) C1 t
  (@additive_terminal_object C Prod t Add) T0 P Q A B X D b c h) (@one_cat_native_snake_six_term_result K C C1
  Prod t Add T0 P Q N A B X D b c h)))) (@finite_arrow_tail_arrow (Functor_cat K C) (@OneCatNativeExactArrowPair
  K C (@additive_preadditive C Prod t Add) C1 t (@additive_terminal_object C Prod t Add) T0 P Q N) (succ zero)
  (@finite_arrow_tail_next (Functor_cat K C) (@OneCatNativeExactArrowPair K C (@additive_preadditive C Prod t
  Add) C1 t (@additive_terminal_object C Prod t Add) T0 P Q N) (succ (succ (succ zero)))
  (@kernel_adjunction_family_func K C (@additive_preadditive C Prod t Add) t (@additive_terminal_object C Prod t
  Add) P (@one_cat_native_snake_alpha_diagram K C (@additive_preadditive C Prod t Add) C1 t
  (@additive_terminal_object C Prod t Add) T0 P A B X D b c h)) (@kernel_adjunction_family_func K C
  (@additive_preadditive C Prod t Add) t (@additive_terminal_object C Prod t Add) P (@transf_arrow_diagram_func
  K C B X b)) (@one_cat_native_snake_kernel_first K C (@additive_preadditive C Prod t Add) C1 t
  (@additive_terminal_object C Prod t Add) T0 P Q A B X D b c h) (@one_cat_native_snake_six_term_result K C C1
  Prod t Add T0 P Q N A B X D b c h)) (@finite_arrow_tail_next (Functor_cat K C) (@OneCatNativeExactArrowPair K
  C (@additive_preadditive C Prod t Add) C1 t (@additive_terminal_object C Prod t Add) T0 P Q N) (succ (succ
  zero)) (@kernel_adjunction_family_func K C (@additive_preadditive C Prod t Add) t (@additive_terminal_object C
  Prod t Add) P (@transf_arrow_diagram_func K C B X b)) (@finite_arrow_tail_next (Functor_cat K C)
  (@OneCatNativeExactArrowPair K C (@additive_preadditive C Prod t Add) C1 t (@additive_terminal_object C Prod t
  Add) T0 P Q N) (succ (succ (succ zero))) (@kernel_adjunction_family_func K C (@additive_preadditive C Prod t
  Add) t (@additive_terminal_object C Prod t Add) P (@one_cat_native_snake_alpha_diagram K C
  (@additive_preadditive C Prod t Add) C1 t (@additive_terminal_object C Prod t Add) T0 P A B X D b c h))
  (@kernel_adjunction_family_func K C (@additive_preadditive C Prod t Add) t (@additive_terminal_object C Prod t
  Add) P (@transf_arrow_diagram_func K C B X b)) (@one_cat_native_snake_kernel_first K C (@additive_preadditive
  C Prod t Add) C1 t (@additive_terminal_object C Prod t Add) T0 P Q A B X D b c h)
  (@one_cat_native_snake_six_term_result K C C1 Prod t Add T0 P Q N A B X D b c h)) (@finite_arrow_tail_arrow
  (Functor_cat K C) (@OneCatNativeExactArrowPair K C (@additive_preadditive C Prod t Add) C1 t
  (@additive_terminal_object C Prod t Add) T0 P Q N) (succ (succ (succ zero))) (@kernel_adjunction_family_func K
  C (@additive_preadditive C Prod t Add) t (@additive_terminal_object C Prod t Add) P
  (@one_cat_native_snake_alpha_diagram K C (@additive_preadditive C Prod t Add) C1 t (@additive_terminal_object
  C Prod t Add) T0 P A B X D b c h)) (@kernel_adjunction_family_func K C (@additive_preadditive C Prod t Add) t
  (@additive_terminal_object C Prod t Add) P (@transf_arrow_diagram_func K C B X b))
  (@one_cat_native_snake_kernel_first K C (@additive_preadditive C Prod t Add) C1 t (@additive_terminal_object C
  Prod t Add) T0 P Q A B X D b c h) (@one_cat_native_snake_six_term_result K C C1 Prod t Add T0 P Q N A B X D b
  c h)) (@finite_arrow_tail_rest (Functor_cat K C) (@OneCatNativeExactArrowPair K C (@additive_preadditive C
  Prod t Add) C1 t (@additive_terminal_object C Prod t Add) T0 P Q N) (succ (succ (succ zero)))
  (@kernel_adjunction_family_func K C (@additive_preadditive C Prod t Add) t (@additive_terminal_object C Prod t
  Add) P (@one_cat_native_snake_alpha_diagram K C (@additive_preadditive C Prod t Add) C1 t
  (@additive_terminal_object C Prod t Add) T0 P A B X D b c h)) (@kernel_adjunction_family_func K C
  (@additive_preadditive C Prod t Add) t (@additive_terminal_object C Prod t Add) P (@transf_arrow_diagram_func
  K C B X b)) (@one_cat_native_snake_kernel_first K C (@additive_preadditive C Prod t Add) C1 t
  (@additive_terminal_object C Prod t Add) T0 P Q A B X D b c h) (@one_cat_native_snake_six_term_result K C C1
  Prod t Add T0 P Q N A B X D b c h))) (@finite_arrow_tail_arrow (Functor_cat K C) (@OneCatNativeExactArrowPair
  K C (@additive_preadditive C Prod t Add) C1 t (@additive_terminal_object C Prod t Add) T0 P Q N) (succ (succ
  zero)) (@kernel_adjunction_family_func K C (@additive_preadditive C Prod t Add) t (@additive_terminal_object C
  Prod t Add) P (@transf_arrow_diagram_func K C B X b)) (@finite_arrow_tail_next (Functor_cat K C)
  (@OneCatNativeExactArrowPair K C (@additive_preadditive C Prod t Add) C1 t (@additive_terminal_object C Prod t
  Add) T0 P Q N) (succ (succ (succ zero))) (@kernel_adjunction_family_func K C (@additive_preadditive C Prod t
  Add) t (@additive_terminal_object C Prod t Add) P (@one_cat_native_snake_alpha_diagram K C
  (@additive_preadditive C Prod t Add) C1 t (@additive_terminal_object C Prod t Add) T0 P A B X D b c h))
  (@kernel_adjunction_family_func K C (@additive_preadditive C Prod t Add) t (@additive_terminal_object C Prod t
  Add) P (@transf_arrow_diagram_func K C B X b)) (@one_cat_native_snake_kernel_first K C (@additive_preadditive
  C Prod t Add) C1 t (@additive_terminal_object C Prod t Add) T0 P Q A B X D b c h)
  (@one_cat_native_snake_six_term_result K C C1 Prod t Add T0 P Q N A B X D b c h)) (@finite_arrow_tail_arrow
  (Functor_cat K C) (@OneCatNativeExactArrowPair K C (@additive_preadditive C Prod t Add) C1 t
  (@additive_terminal_object C Prod t Add) T0 P Q N) (succ (succ (succ zero))) (@kernel_adjunction_family_func K
  C (@additive_preadditive C Prod t Add) t (@additive_terminal_object C Prod t Add) P
  (@one_cat_native_snake_alpha_diagram K C (@additive_preadditive C Prod t Add) C1 t (@additive_terminal_object
  C Prod t Add) T0 P A B X D b c h)) (@kernel_adjunction_family_func K C (@additive_preadditive C Prod t Add) t
  (@additive_terminal_object C Prod t Add) P (@transf_arrow_diagram_func K C B X b))
  (@one_cat_native_snake_kernel_first K C (@additive_preadditive C Prod t Add) C1 t (@additive_terminal_object C
  Prod t Add) T0 P Q A B X D b c h) (@one_cat_native_snake_six_term_result K C C1 Prod t Add T0 P Q N A B X D b
  c h)) (@finite_arrow_tail_rest (Functor_cat K C) (@OneCatNativeExactArrowPair K C (@additive_preadditive C
  Prod t Add) C1 t (@additive_terminal_object C Prod t Add) T0 P Q N) (succ (succ (succ zero)))
  (@kernel_adjunction_family_func K C (@additive_preadditive C Prod t Add) t (@additive_terminal_object C Prod t
  Add) P (@one_cat_native_snake_alpha_diagram K C (@additive_preadditive C Prod t Add) C1 t
  (@additive_terminal_object C Prod t Add) T0 P A B X D b c h)) (@kernel_adjunction_family_func K C
  (@additive_preadditive C Prod t Add) t (@additive_terminal_object C Prod t Add) P (@transf_arrow_diagram_func
  K C B X b)) (@one_cat_native_snake_kernel_first K C (@additive_preadditive C Prod t Add) C1 t
  (@additive_terminal_object C Prod t Add) T0 P Q A B X D b c h) (@one_cat_native_snake_six_term_result K C C1
  Prod t Add T0 P Q N A B X D b c h))) (@finite_arrow_tail_rest (Functor_cat K C) (@OneCatNativeExactArrowPair K
  C (@additive_preadditive C Prod t Add) C1 t (@additive_terminal_object C Prod t Add) T0 P Q N) (succ (succ
  zero)) (@kernel_adjunction_family_func K C (@additive_preadditive C Prod t Add) t (@additive_terminal_object C
  Prod t Add) P (@transf_arrow_diagram_func K C B X b)) (@finite_arrow_tail_next (Functor_cat K C)
  (@OneCatNativeExactArrowPair K C (@additive_preadditive C Prod t Add) C1 t (@additive_terminal_object C Prod t
  Add) T0 P Q N) (succ (succ (succ zero))) (@kernel_adjunction_family_func K C (@additive_preadditive C Prod t
  Add) t (@additive_terminal_object C Prod t Add) P (@one_cat_native_snake_alpha_diagram K C
  (@additive_preadditive C Prod t Add) C1 t (@additive_terminal_object C Prod t Add) T0 P A B X D b c h))
  (@kernel_adjunction_family_func K C (@additive_preadditive C Prod t Add) t (@additive_terminal_object C Prod t
  Add) P (@transf_arrow_diagram_func K C B X b)) (@one_cat_native_snake_kernel_first K C (@additive_preadditive
  C Prod t Add) C1 t (@additive_terminal_object C Prod t Add) T0 P Q A B X D b c h)
  (@one_cat_native_snake_six_term_result K C C1 Prod t Add T0 P Q N A B X D b c h)) (@finite_arrow_tail_arrow
  (Functor_cat K C) (@OneCatNativeExactArrowPair K C (@additive_preadditive C Prod t Add) C1 t
  (@additive_terminal_object C Prod t Add) T0 P Q N) (succ (succ (succ zero))) (@kernel_adjunction_family_func K
  C (@additive_preadditive C Prod t Add) t (@additive_terminal_object C Prod t Add) P
  (@one_cat_native_snake_alpha_diagram K C (@additive_preadditive C Prod t Add) C1 t (@additive_terminal_object
  C Prod t Add) T0 P A B X D b c h)) (@kernel_adjunction_family_func K C (@additive_preadditive C Prod t Add) t
  (@additive_terminal_object C Prod t Add) P (@transf_arrow_diagram_func K C B X b))
  (@one_cat_native_snake_kernel_first K C (@additive_preadditive C Prod t Add) C1 t (@additive_terminal_object C
  Prod t Add) T0 P Q A B X D b c h) (@one_cat_native_snake_six_term_result K C C1 Prod t Add T0 P Q N A B X D b
  c h)) (@finite_arrow_tail_rest (Functor_cat K C) (@OneCatNativeExactArrowPair K C (@additive_preadditive C
  Prod t Add) C1 t (@additive_terminal_object C Prod t Add) T0 P Q N) (succ (succ (succ zero)))
  (@kernel_adjunction_family_func K C (@additive_preadditive C Prod t Add) t (@additive_terminal_object C Prod t
  Add) P (@one_cat_native_snake_alpha_diagram K C (@additive_preadditive C Prod t Add) C1 t
  (@additive_terminal_object C Prod t Add) T0 P A B X D b c h)) (@kernel_adjunction_family_func K C
  (@additive_preadditive C Prod t Add) t (@additive_terminal_object C Prod t Add) P (@transf_arrow_diagram_func
  K C B X b)) (@one_cat_native_snake_kernel_first K C (@additive_preadditive C Prod t Add) C1 t
  (@additive_terminal_object C Prod t Add) T0 P Q A B X D b c h) (@one_cat_native_snake_six_term_result K C C1
  Prod t Add T0 P Q N A B X D b c h)))) (@finite_arrow_tail_rest (Functor_cat K C) (@OneCatNativeExactArrowPair
  K C (@additive_preadditive C Prod t Add) C1 t (@additive_terminal_object C Prod t Add) T0 P Q N) (succ zero)
  (@finite_arrow_tail_next (Functor_cat K C) (@OneCatNativeExactArrowPair K C (@additive_preadditive C Prod t
  Add) C1 t (@additive_terminal_object C Prod t Add) T0 P Q N) (succ (succ (succ zero)))
  (@kernel_adjunction_family_func K C (@additive_preadditive C Prod t Add) t (@additive_terminal_object C Prod t
  Add) P (@one_cat_native_snake_alpha_diagram K C (@additive_preadditive C Prod t Add) C1 t
  (@additive_terminal_object C Prod t Add) T0 P A B X D b c h)) (@kernel_adjunction_family_func K C
  (@additive_preadditive C Prod t Add) t (@additive_terminal_object C Prod t Add) P (@transf_arrow_diagram_func
  K C B X b)) (@one_cat_native_snake_kernel_first K C (@additive_preadditive C Prod t Add) C1 t
  (@additive_terminal_object C Prod t Add) T0 P Q A B X D b c h) (@one_cat_native_snake_six_term_result K C C1
  Prod t Add T0 P Q N A B X D b c h)) (@finite_arrow_tail_next (Functor_cat K C) (@OneCatNativeExactArrowPair K
  C (@additive_preadditive C Prod t Add) C1 t (@additive_terminal_object C Prod t Add) T0 P Q N) (succ (succ
  zero)) (@kernel_adjunction_family_func K C (@additive_preadditive C Prod t Add) t (@additive_terminal_object C
  Prod t Add) P (@transf_arrow_diagram_func K C B X b)) (@finite_arrow_tail_next (Functor_cat K C)
  (@OneCatNativeExactArrowPair K C (@additive_preadditive C Prod t Add) C1 t (@additive_terminal_object C Prod t
  Add) T0 P Q N) (succ (succ (succ zero))) (@kernel_adjunction_family_func K C (@additive_preadditive C Prod t
  Add) t (@additive_terminal_object C Prod t Add) P (@one_cat_native_snake_alpha_diagram K C
  (@additive_preadditive C Prod t Add) C1 t (@additive_terminal_object C Prod t Add) T0 P A B X D b c h))
  (@kernel_adjunction_family_func K C (@additive_preadditive C Prod t Add) t (@additive_terminal_object C Prod t
  Add) P (@transf_arrow_diagram_func K C B X b)) (@one_cat_native_snake_kernel_first K C (@additive_preadditive
  C Prod t Add) C1 t (@additive_terminal_object C Prod t Add) T0 P Q A B X D b c h)
  (@one_cat_native_snake_six_term_result K C C1 Prod t Add T0 P Q N A B X D b c h)) (@finite_arrow_tail_arrow
  (Functor_cat K C) (@OneCatNativeExactArrowPair K C (@additive_preadditive C Prod t Add) C1 t
  (@additive_terminal_object C Prod t Add) T0 P Q N) (succ (succ (succ zero))) (@kernel_adjunction_family_func K
  C (@additive_preadditive C Prod t Add) t (@additive_terminal_object C Prod t Add) P
  (@one_cat_native_snake_alpha_diagram K C (@additive_preadditive C Prod t Add) C1 t (@additive_terminal_object
  C Prod t Add) T0 P A B X D b c h)) (@kernel_adjunction_family_func K C (@additive_preadditive C Prod t Add) t
  (@additive_terminal_object C Prod t Add) P (@transf_arrow_diagram_func K C B X b))
  (@one_cat_native_snake_kernel_first K C (@additive_preadditive C Prod t Add) C1 t (@additive_terminal_object C
  Prod t Add) T0 P Q A B X D b c h) (@one_cat_native_snake_six_term_result K C C1 Prod t Add T0 P Q N A B X D b
  c h)) (@finite_arrow_tail_rest (Functor_cat K C) (@OneCatNativeExactArrowPair K C (@additive_preadditive C
  Prod t Add) C1 t (@additive_terminal_object C Prod t Add) T0 P Q N) (succ (succ (succ zero)))
  (@kernel_adjunction_family_func K C (@additive_preadditive C Prod t Add) t (@additive_terminal_object C Prod t
  Add) P (@one_cat_native_snake_alpha_diagram K C (@additive_preadditive C Prod t Add) C1 t
  (@additive_terminal_object C Prod t Add) T0 P A B X D b c h)) (@kernel_adjunction_family_func K C
  (@additive_preadditive C Prod t Add) t (@additive_terminal_object C Prod t Add) P (@transf_arrow_diagram_func
  K C B X b)) (@one_cat_native_snake_kernel_first K C (@additive_preadditive C Prod t Add) C1 t
  (@additive_terminal_object C Prod t Add) T0 P Q A B X D b c h) (@one_cat_native_snake_six_term_result K C C1
  Prod t Add T0 P Q N A B X D b c h))) (@finite_arrow_tail_arrow (Functor_cat K C) (@OneCatNativeExactArrowPair
  K C (@additive_preadditive C Prod t Add) C1 t (@additive_terminal_object C Prod t Add) T0 P Q N) (succ (succ
  zero)) (@kernel_adjunction_family_func K C (@additive_preadditive C Prod t Add) t (@additive_terminal_object C
  Prod t Add) P (@transf_arrow_diagram_func K C B X b)) (@finite_arrow_tail_next (Functor_cat K C)
  (@OneCatNativeExactArrowPair K C (@additive_preadditive C Prod t Add) C1 t (@additive_terminal_object C Prod t
  Add) T0 P Q N) (succ (succ (succ zero))) (@kernel_adjunction_family_func K C (@additive_preadditive C Prod t
  Add) t (@additive_terminal_object C Prod t Add) P (@one_cat_native_snake_alpha_diagram K C
  (@additive_preadditive C Prod t Add) C1 t (@additive_terminal_object C Prod t Add) T0 P A B X D b c h))
  (@kernel_adjunction_family_func K C (@additive_preadditive C Prod t Add) t (@additive_terminal_object C Prod t
  Add) P (@transf_arrow_diagram_func K C B X b)) (@one_cat_native_snake_kernel_first K C (@additive_preadditive
  C Prod t Add) C1 t (@additive_terminal_object C Prod t Add) T0 P Q A B X D b c h)
  (@one_cat_native_snake_six_term_result K C C1 Prod t Add T0 P Q N A B X D b c h)) (@finite_arrow_tail_arrow
  (Functor_cat K C) (@OneCatNativeExactArrowPair K C (@additive_preadditive C Prod t Add) C1 t
  (@additive_terminal_object C Prod t Add) T0 P Q N) (succ (succ (succ zero))) (@kernel_adjunction_family_func K
  C (@additive_preadditive C Prod t Add) t (@additive_terminal_object C Prod t Add) P
  (@one_cat_native_snake_alpha_diagram K C (@additive_preadditive C Prod t Add) C1 t (@additive_terminal_object
  C Prod t Add) T0 P A B X D b c h)) (@kernel_adjunction_family_func K C (@additive_preadditive C Prod t Add) t
  (@additive_terminal_object C Prod t Add) P (@transf_arrow_diagram_func K C B X b))
  (@one_cat_native_snake_kernel_first K C (@additive_preadditive C Prod t Add) C1 t (@additive_terminal_object C
  Prod t Add) T0 P Q A B X D b c h) (@one_cat_native_snake_six_term_result K C C1 Prod t Add T0 P Q N A B X D b
  c h)) (@finite_arrow_tail_rest (Functor_cat K C) (@OneCatNativeExactArrowPair K C (@additive_preadditive C
  Prod t Add) C1 t (@additive_terminal_object C Prod t Add) T0 P Q N) (succ (succ (succ zero)))
  (@kernel_adjunction_family_func K C (@additive_preadditive C Prod t Add) t (@additive_terminal_object C Prod t
  Add) P (@one_cat_native_snake_alpha_diagram K C (@additive_preadditive C Prod t Add) C1 t
  (@additive_terminal_object C Prod t Add) T0 P A B X D b c h)) (@kernel_adjunction_family_func K C
  (@additive_preadditive C Prod t Add) t (@additive_terminal_object C Prod t Add) P (@transf_arrow_diagram_func
  K C B X b)) (@one_cat_native_snake_kernel_first K C (@additive_preadditive C Prod t Add) C1 t
  (@additive_terminal_object C Prod t Add) T0 P Q A B X D b c h) (@one_cat_native_snake_six_term_result K C C1
  Prod t Add T0 P Q N A B X D b c h))) (@finite_arrow_tail_rest (Functor_cat K C) (@OneCatNativeExactArrowPair K
  C (@additive_preadditive C Prod t Add) C1 t (@additive_terminal_object C Prod t Add) T0 P Q N) (succ (succ
  zero)) (@kernel_adjunction_family_func K C (@additive_preadditive C Prod t Add) t (@additive_terminal_object C
  Prod t Add) P (@transf_arrow_diagram_func K C B X b)) (@finite_arrow_tail_next (Functor_cat K C)
  (@OneCatNativeExactArrowPair K C (@additive_preadditive C Prod t Add) C1 t (@additive_terminal_object C Prod t
  Add) T0 P Q N) (succ (succ (succ zero))) (@kernel_adjunction_family_func K C (@additive_preadditive C Prod t
  Add) t (@additive_terminal_object C Prod t Add) P (@one_cat_native_snake_alpha_diagram K C
  (@additive_preadditive C Prod t Add) C1 t (@additive_terminal_object C Prod t Add) T0 P A B X D b c h))
  (@kernel_adjunction_family_func K C (@additive_preadditive C Prod t Add) t (@additive_terminal_object C Prod t
  Add) P (@transf_arrow_diagram_func K C B X b)) (@one_cat_native_snake_kernel_first K C (@additive_preadditive
  C Prod t Add) C1 t (@additive_terminal_object C Prod t Add) T0 P Q A B X D b c h)
  (@one_cat_native_snake_six_term_result K C C1 Prod t Add T0 P Q N A B X D b c h)) (@finite_arrow_tail_arrow
  (Functor_cat K C) (@OneCatNativeExactArrowPair K C (@additive_preadditive C Prod t Add) C1 t
  (@additive_terminal_object C Prod t Add) T0 P Q N) (succ (succ (succ zero))) (@kernel_adjunction_family_func K
  C (@additive_preadditive C Prod t Add) t (@additive_terminal_object C Prod t Add) P
  (@one_cat_native_snake_alpha_diagram K C (@additive_preadditive C Prod t Add) C1 t (@additive_terminal_object
  C Prod t Add) T0 P A B X D b c h)) (@kernel_adjunction_family_func K C (@additive_preadditive C Prod t Add) t
  (@additive_terminal_object C Prod t Add) P (@transf_arrow_diagram_func K C B X b))
  (@one_cat_native_snake_kernel_first K C (@additive_preadditive C Prod t Add) C1 t (@additive_terminal_object C
  Prod t Add) T0 P Q A B X D b c h) (@one_cat_native_snake_six_term_result K C C1 Prod t Add T0 P Q N A B X D b
  c h)) (@finite_arrow_tail_rest (Functor_cat K C) (@OneCatNativeExactArrowPair K C (@additive_preadditive C
  Prod t Add) C1 t (@additive_terminal_object C Prod t Add) T0 P Q N) (succ (succ (succ zero)))
  (@kernel_adjunction_family_func K C (@additive_preadditive C Prod t Add) t (@additive_terminal_object C Prod t
  Add) P (@one_cat_native_snake_alpha_diagram K C (@additive_preadditive C Prod t Add) C1 t
  (@additive_terminal_object C Prod t Add) T0 P A B X D b c h)) (@kernel_adjunction_family_func K C
  (@additive_preadditive C Prod t Add) t (@additive_terminal_object C Prod t Add) P (@transf_arrow_diagram_func
  K C B X b)) (@one_cat_native_snake_kernel_first K C (@additive_preadditive C Prod t Add) C1 t
  (@additive_terminal_object C Prod t Add) T0 P Q A B X D b c h) (@one_cat_native_snake_six_term_result K C C1
  Prod t Add T0 P Q N A B X D b c h))))) (@finite_arrow_tail_step (Functor_cat K C) (@OneCatNativeExactArrowPair
  K C (@additive_preadditive C Prod t Add) C1 t (@additive_terminal_object C Prod t Add) T0 P Q N) zero
  (@finite_arrow_tail_next (Functor_cat K C) (@OneCatNativeExactArrowPair K C (@additive_preadditive C Prod t
  Add) C1 t (@additive_terminal_object C Prod t Add) T0 P Q N) (succ (succ zero))
  (@kernel_adjunction_family_func K C (@additive_preadditive C Prod t Add) t (@additive_terminal_object C Prod t
  Add) P (@transf_arrow_diagram_func K C B X b)) (@finite_arrow_tail_next (Functor_cat K C)
  (@OneCatNativeExactArrowPair K C (@additive_preadditive C Prod t Add) C1 t (@additive_terminal_object C Prod t
  Add) T0 P Q N) (succ (succ (succ zero))) (@kernel_adjunction_family_func K C (@additive_preadditive C Prod t
  Add) t (@additive_terminal_object C Prod t Add) P (@one_cat_native_snake_alpha_diagram K C
  (@additive_preadditive C Prod t Add) C1 t (@additive_terminal_object C Prod t Add) T0 P A B X D b c h))
  (@kernel_adjunction_family_func K C (@additive_preadditive C Prod t Add) t (@additive_terminal_object C Prod t
  Add) P (@transf_arrow_diagram_func K C B X b)) (@one_cat_native_snake_kernel_first K C (@additive_preadditive
  C Prod t Add) C1 t (@additive_terminal_object C Prod t Add) T0 P Q A B X D b c h)
  (@one_cat_native_snake_six_term_result K C C1 Prod t Add T0 P Q N A B X D b c h)) (@finite_arrow_tail_arrow
  (Functor_cat K C) (@OneCatNativeExactArrowPair K C (@additive_preadditive C Prod t Add) C1 t
  (@additive_terminal_object C Prod t Add) T0 P Q N) (succ (succ (succ zero))) (@kernel_adjunction_family_func K
  C (@additive_preadditive C Prod t Add) t (@additive_terminal_object C Prod t Add) P
  (@one_cat_native_snake_alpha_diagram K C (@additive_preadditive C Prod t Add) C1 t (@additive_terminal_object
  C Prod t Add) T0 P A B X D b c h)) (@kernel_adjunction_family_func K C (@additive_preadditive C Prod t Add) t
  (@additive_terminal_object C Prod t Add) P (@transf_arrow_diagram_func K C B X b))
  (@one_cat_native_snake_kernel_first K C (@additive_preadditive C Prod t Add) C1 t (@additive_terminal_object C
  Prod t Add) T0 P Q A B X D b c h) (@one_cat_native_snake_six_term_result K C C1 Prod t Add T0 P Q N A B X D b
  c h)) (@finite_arrow_tail_rest (Functor_cat K C) (@OneCatNativeExactArrowPair K C (@additive_preadditive C
  Prod t Add) C1 t (@additive_terminal_object C Prod t Add) T0 P Q N) (succ (succ (succ zero)))
  (@kernel_adjunction_family_func K C (@additive_preadditive C Prod t Add) t (@additive_terminal_object C Prod t
  Add) P (@one_cat_native_snake_alpha_diagram K C (@additive_preadditive C Prod t Add) C1 t
  (@additive_terminal_object C Prod t Add) T0 P A B X D b c h)) (@kernel_adjunction_family_func K C
  (@additive_preadditive C Prod t Add) t (@additive_terminal_object C Prod t Add) P (@transf_arrow_diagram_func
  K C B X b)) (@one_cat_native_snake_kernel_first K C (@additive_preadditive C Prod t Add) C1 t
  (@additive_terminal_object C Prod t Add) T0 P Q A B X D b c h) (@one_cat_native_snake_six_term_result K C C1
  Prod t Add T0 P Q N A B X D b c h))) (@finite_arrow_tail_next (Functor_cat K C) (@OneCatNativeExactArrowPair K
  C (@additive_preadditive C Prod t Add) C1 t (@additive_terminal_object C Prod t Add) T0 P Q N) (succ zero)
  (@finite_arrow_tail_next (Functor_cat K C) (@OneCatNativeExactArrowPair K C (@additive_preadditive C Prod t
  Add) C1 t (@additive_terminal_object C Prod t Add) T0 P Q N) (succ (succ (succ zero)))
  (@kernel_adjunction_family_func K C (@additive_preadditive C Prod t Add) t (@additive_terminal_object C Prod t
  Add) P (@one_cat_native_snake_alpha_diagram K C (@additive_preadditive C Prod t Add) C1 t
  (@additive_terminal_object C Prod t Add) T0 P A B X D b c h)) (@kernel_adjunction_family_func K C
  (@additive_preadditive C Prod t Add) t (@additive_terminal_object C Prod t Add) P (@transf_arrow_diagram_func
  K C B X b)) (@one_cat_native_snake_kernel_first K C (@additive_preadditive C Prod t Add) C1 t
  (@additive_terminal_object C Prod t Add) T0 P Q A B X D b c h) (@one_cat_native_snake_six_term_result K C C1
  Prod t Add T0 P Q N A B X D b c h)) (@finite_arrow_tail_next (Functor_cat K C) (@OneCatNativeExactArrowPair K
  C (@additive_preadditive C Prod t Add) C1 t (@additive_terminal_object C Prod t Add) T0 P Q N) (succ (succ
  zero)) (@kernel_adjunction_family_func K C (@additive_preadditive C Prod t Add) t (@additive_terminal_object C
  Prod t Add) P (@transf_arrow_diagram_func K C B X b)) (@finite_arrow_tail_next (Functor_cat K C)
  (@OneCatNativeExactArrowPair K C (@additive_preadditive C Prod t Add) C1 t (@additive_terminal_object C Prod t
  Add) T0 P Q N) (succ (succ (succ zero))) (@kernel_adjunction_family_func K C (@additive_preadditive C Prod t
  Add) t (@additive_terminal_object C Prod t Add) P (@one_cat_native_snake_alpha_diagram K C
  (@additive_preadditive C Prod t Add) C1 t (@additive_terminal_object C Prod t Add) T0 P A B X D b c h))
  (@kernel_adjunction_family_func K C (@additive_preadditive C Prod t Add) t (@additive_terminal_object C Prod t
  Add) P (@transf_arrow_diagram_func K C B X b)) (@one_cat_native_snake_kernel_first K C (@additive_preadditive
  C Prod t Add) C1 t (@additive_terminal_object C Prod t Add) T0 P Q A B X D b c h)
  (@one_cat_native_snake_six_term_result K C C1 Prod t Add T0 P Q N A B X D b c h)) (@finite_arrow_tail_arrow
  (Functor_cat K C) (@OneCatNativeExactArrowPair K C (@additive_preadditive C Prod t Add) C1 t
  (@additive_terminal_object C Prod t Add) T0 P Q N) (succ (succ (succ zero))) (@kernel_adjunction_family_func K
  C (@additive_preadditive C Prod t Add) t (@additive_terminal_object C Prod t Add) P
  (@one_cat_native_snake_alpha_diagram K C (@additive_preadditive C Prod t Add) C1 t (@additive_terminal_object
  C Prod t Add) T0 P A B X D b c h)) (@kernel_adjunction_family_func K C (@additive_preadditive C Prod t Add) t
  (@additive_terminal_object C Prod t Add) P (@transf_arrow_diagram_func K C B X b))
  (@one_cat_native_snake_kernel_first K C (@additive_preadditive C Prod t Add) C1 t (@additive_terminal_object C
  Prod t Add) T0 P Q A B X D b c h) (@one_cat_native_snake_six_term_result K C C1 Prod t Add T0 P Q N A B X D b
  c h)) (@finite_arrow_tail_rest (Functor_cat K C) (@OneCatNativeExactArrowPair K C (@additive_preadditive C
  Prod t Add) C1 t (@additive_terminal_object C Prod t Add) T0 P Q N) (succ (succ (succ zero)))
  (@kernel_adjunction_family_func K C (@additive_preadditive C Prod t Add) t (@additive_terminal_object C Prod t
  Add) P (@one_cat_native_snake_alpha_diagram K C (@additive_preadditive C Prod t Add) C1 t
  (@additive_terminal_object C Prod t Add) T0 P A B X D b c h)) (@kernel_adjunction_family_func K C
  (@additive_preadditive C Prod t Add) t (@additive_terminal_object C Prod t Add) P (@transf_arrow_diagram_func
  K C B X b)) (@one_cat_native_snake_kernel_first K C (@additive_preadditive C Prod t Add) C1 t
  (@additive_terminal_object C Prod t Add) T0 P Q A B X D b c h) (@one_cat_native_snake_six_term_result K C C1
  Prod t Add T0 P Q N A B X D b c h))) (@finite_arrow_tail_arrow (Functor_cat K C) (@OneCatNativeExactArrowPair
  K C (@additive_preadditive C Prod t Add) C1 t (@additive_terminal_object C Prod t Add) T0 P Q N) (succ (succ
  zero)) (@kernel_adjunction_family_func K C (@additive_preadditive C Prod t Add) t (@additive_terminal_object C
  Prod t Add) P (@transf_arrow_diagram_func K C B X b)) (@finite_arrow_tail_next (Functor_cat K C)
  (@OneCatNativeExactArrowPair K C (@additive_preadditive C Prod t Add) C1 t (@additive_terminal_object C Prod t
  Add) T0 P Q N) (succ (succ (succ zero))) (@kernel_adjunction_family_func K C (@additive_preadditive C Prod t
  Add) t (@additive_terminal_object C Prod t Add) P (@one_cat_native_snake_alpha_diagram K C
  (@additive_preadditive C Prod t Add) C1 t (@additive_terminal_object C Prod t Add) T0 P A B X D b c h))
  (@kernel_adjunction_family_func K C (@additive_preadditive C Prod t Add) t (@additive_terminal_object C Prod t
  Add) P (@transf_arrow_diagram_func K C B X b)) (@one_cat_native_snake_kernel_first K C (@additive_preadditive
  C Prod t Add) C1 t (@additive_terminal_object C Prod t Add) T0 P Q A B X D b c h)
  (@one_cat_native_snake_six_term_result K C C1 Prod t Add T0 P Q N A B X D b c h)) (@finite_arrow_tail_arrow
  (Functor_cat K C) (@OneCatNativeExactArrowPair K C (@additive_preadditive C Prod t Add) C1 t
  (@additive_terminal_object C Prod t Add) T0 P Q N) (succ (succ (succ zero))) (@kernel_adjunction_family_func K
  C (@additive_preadditive C Prod t Add) t (@additive_terminal_object C Prod t Add) P
  (@one_cat_native_snake_alpha_diagram K C (@additive_preadditive C Prod t Add) C1 t (@additive_terminal_object
  C Prod t Add) T0 P A B X D b c h)) (@kernel_adjunction_family_func K C (@additive_preadditive C Prod t Add) t
  (@additive_terminal_object C Prod t Add) P (@transf_arrow_diagram_func K C B X b))
  (@one_cat_native_snake_kernel_first K C (@additive_preadditive C Prod t Add) C1 t (@additive_terminal_object C
  Prod t Add) T0 P Q A B X D b c h) (@one_cat_native_snake_six_term_result K C C1 Prod t Add T0 P Q N A B X D b
  c h)) (@finite_arrow_tail_rest (Functor_cat K C) (@OneCatNativeExactArrowPair K C (@additive_preadditive C
  Prod t Add) C1 t (@additive_terminal_object C Prod t Add) T0 P Q N) (succ (succ (succ zero)))
  (@kernel_adjunction_family_func K C (@additive_preadditive C Prod t Add) t (@additive_terminal_object C Prod t
  Add) P (@one_cat_native_snake_alpha_diagram K C (@additive_preadditive C Prod t Add) C1 t
  (@additive_terminal_object C Prod t Add) T0 P A B X D b c h)) (@kernel_adjunction_family_func K C
  (@additive_preadditive C Prod t Add) t (@additive_terminal_object C Prod t Add) P (@transf_arrow_diagram_func
  K C B X b)) (@one_cat_native_snake_kernel_first K C (@additive_preadditive C Prod t Add) C1 t
  (@additive_terminal_object C Prod t Add) T0 P Q A B X D b c h) (@one_cat_native_snake_six_term_result K C C1
  Prod t Add T0 P Q N A B X D b c h))) (@finite_arrow_tail_rest (Functor_cat K C) (@OneCatNativeExactArrowPair K
  C (@additive_preadditive C Prod t Add) C1 t (@additive_terminal_object C Prod t Add) T0 P Q N) (succ (succ
  zero)) (@kernel_adjunction_family_func K C (@additive_preadditive C Prod t Add) t (@additive_terminal_object C
  Prod t Add) P (@transf_arrow_diagram_func K C B X b)) (@finite_arrow_tail_next (Functor_cat K C)
  (@OneCatNativeExactArrowPair K C (@additive_preadditive C Prod t Add) C1 t (@additive_terminal_object C Prod t
  Add) T0 P Q N) (succ (succ (succ zero))) (@kernel_adjunction_family_func K C (@additive_preadditive C Prod t
  Add) t (@additive_terminal_object C Prod t Add) P (@one_cat_native_snake_alpha_diagram K C
  (@additive_preadditive C Prod t Add) C1 t (@additive_terminal_object C Prod t Add) T0 P A B X D b c h))
  (@kernel_adjunction_family_func K C (@additive_preadditive C Prod t Add) t (@additive_terminal_object C Prod t
  Add) P (@transf_arrow_diagram_func K C B X b)) (@one_cat_native_snake_kernel_first K C (@additive_preadditive
  C Prod t Add) C1 t (@additive_terminal_object C Prod t Add) T0 P Q A B X D b c h)
  (@one_cat_native_snake_six_term_result K C C1 Prod t Add T0 P Q N A B X D b c h)) (@finite_arrow_tail_arrow
  (Functor_cat K C) (@OneCatNativeExactArrowPair K C (@additive_preadditive C Prod t Add) C1 t
  (@additive_terminal_object C Prod t Add) T0 P Q N) (succ (succ (succ zero))) (@kernel_adjunction_family_func K
  C (@additive_preadditive C Prod t Add) t (@additive_terminal_object C Prod t Add) P
  (@one_cat_native_snake_alpha_diagram K C (@additive_preadditive C Prod t Add) C1 t (@additive_terminal_object
  C Prod t Add) T0 P A B X D b c h)) (@kernel_adjunction_family_func K C (@additive_preadditive C Prod t Add) t
  (@additive_terminal_object C Prod t Add) P (@transf_arrow_diagram_func K C B X b))
  (@one_cat_native_snake_kernel_first K C (@additive_preadditive C Prod t Add) C1 t (@additive_terminal_object C
  Prod t Add) T0 P Q A B X D b c h) (@one_cat_native_snake_six_term_result K C C1 Prod t Add T0 P Q N A B X D b
  c h)) (@finite_arrow_tail_rest (Functor_cat K C) (@OneCatNativeExactArrowPair K C (@additive_preadditive C
  Prod t Add) C1 t (@additive_terminal_object C Prod t Add) T0 P Q N) (succ (succ (succ zero)))
  (@kernel_adjunction_family_func K C (@additive_preadditive C Prod t Add) t (@additive_terminal_object C Prod t
  Add) P (@one_cat_native_snake_alpha_diagram K C (@additive_preadditive C Prod t Add) C1 t
  (@additive_terminal_object C Prod t Add) T0 P A B X D b c h)) (@kernel_adjunction_family_func K C
  (@additive_preadditive C Prod t Add) t (@additive_terminal_object C Prod t Add) P (@transf_arrow_diagram_func
  K C B X b)) (@one_cat_native_snake_kernel_first K C (@additive_preadditive C Prod t Add) C1 t
  (@additive_terminal_object C Prod t Add) T0 P Q A B X D b c h) (@one_cat_native_snake_six_term_result K C C1
  Prod t Add T0 P Q N A B X D b c h)))) (@finite_arrow_tail_arrow (Functor_cat K C) (@OneCatNativeExactArrowPair
  K C (@additive_preadditive C Prod t Add) C1 t (@additive_terminal_object C Prod t Add) T0 P Q N) (succ zero)
  (@finite_arrow_tail_next (Functor_cat K C) (@OneCatNativeExactArrowPair K C (@additive_preadditive C Prod t
  Add) C1 t (@additive_terminal_object C Prod t Add) T0 P Q N) (succ (succ (succ zero)))
  (@kernel_adjunction_family_func K C (@additive_preadditive C Prod t Add) t (@additive_terminal_object C Prod t
  Add) P (@one_cat_native_snake_alpha_diagram K C (@additive_preadditive C Prod t Add) C1 t
  (@additive_terminal_object C Prod t Add) T0 P A B X D b c h)) (@kernel_adjunction_family_func K C
  (@additive_preadditive C Prod t Add) t (@additive_terminal_object C Prod t Add) P (@transf_arrow_diagram_func
  K C B X b)) (@one_cat_native_snake_kernel_first K C (@additive_preadditive C Prod t Add) C1 t
  (@additive_terminal_object C Prod t Add) T0 P Q A B X D b c h) (@one_cat_native_snake_six_term_result K C C1
  Prod t Add T0 P Q N A B X D b c h)) (@finite_arrow_tail_next (Functor_cat K C) (@OneCatNativeExactArrowPair K
  C (@additive_preadditive C Prod t Add) C1 t (@additive_terminal_object C Prod t Add) T0 P Q N) (succ (succ
  zero)) (@kernel_adjunction_family_func K C (@additive_preadditive C Prod t Add) t (@additive_terminal_object C
  Prod t Add) P (@transf_arrow_diagram_func K C B X b)) (@finite_arrow_tail_next (Functor_cat K C)
  (@OneCatNativeExactArrowPair K C (@additive_preadditive C Prod t Add) C1 t (@additive_terminal_object C Prod t
  Add) T0 P Q N) (succ (succ (succ zero))) (@kernel_adjunction_family_func K C (@additive_preadditive C Prod t
  Add) t (@additive_terminal_object C Prod t Add) P (@one_cat_native_snake_alpha_diagram K C
  (@additive_preadditive C Prod t Add) C1 t (@additive_terminal_object C Prod t Add) T0 P A B X D b c h))
  (@kernel_adjunction_family_func K C (@additive_preadditive C Prod t Add) t (@additive_terminal_object C Prod t
  Add) P (@transf_arrow_diagram_func K C B X b)) (@one_cat_native_snake_kernel_first K C (@additive_preadditive
  C Prod t Add) C1 t (@additive_terminal_object C Prod t Add) T0 P Q A B X D b c h)
  (@one_cat_native_snake_six_term_result K C C1 Prod t Add T0 P Q N A B X D b c h)) (@finite_arrow_tail_arrow
  (Functor_cat K C) (@OneCatNativeExactArrowPair K C (@additive_preadditive C Prod t Add) C1 t
  (@additive_terminal_object C Prod t Add) T0 P Q N) (succ (succ (succ zero))) (@kernel_adjunction_family_func K
  C (@additive_preadditive C Prod t Add) t (@additive_terminal_object C Prod t Add) P
  (@one_cat_native_snake_alpha_diagram K C (@additive_preadditive C Prod t Add) C1 t (@additive_terminal_object
  C Prod t Add) T0 P A B X D b c h)) (@kernel_adjunction_family_func K C (@additive_preadditive C Prod t Add) t
  (@additive_terminal_object C Prod t Add) P (@transf_arrow_diagram_func K C B X b))
  (@one_cat_native_snake_kernel_first K C (@additive_preadditive C Prod t Add) C1 t (@additive_terminal_object C
  Prod t Add) T0 P Q A B X D b c h) (@one_cat_native_snake_six_term_result K C C1 Prod t Add T0 P Q N A B X D b
  c h)) (@finite_arrow_tail_rest (Functor_cat K C) (@OneCatNativeExactArrowPair K C (@additive_preadditive C
  Prod t Add) C1 t (@additive_terminal_object C Prod t Add) T0 P Q N) (succ (succ (succ zero)))
  (@kernel_adjunction_family_func K C (@additive_preadditive C Prod t Add) t (@additive_terminal_object C Prod t
  Add) P (@one_cat_native_snake_alpha_diagram K C (@additive_preadditive C Prod t Add) C1 t
  (@additive_terminal_object C Prod t Add) T0 P A B X D b c h)) (@kernel_adjunction_family_func K C
  (@additive_preadditive C Prod t Add) t (@additive_terminal_object C Prod t Add) P (@transf_arrow_diagram_func
  K C B X b)) (@one_cat_native_snake_kernel_first K C (@additive_preadditive C Prod t Add) C1 t
  (@additive_terminal_object C Prod t Add) T0 P Q A B X D b c h) (@one_cat_native_snake_six_term_result K C C1
  Prod t Add T0 P Q N A B X D b c h))) (@finite_arrow_tail_arrow (Functor_cat K C) (@OneCatNativeExactArrowPair
  K C (@additive_preadditive C Prod t Add) C1 t (@additive_terminal_object C Prod t Add) T0 P Q N) (succ (succ
  zero)) (@kernel_adjunction_family_func K C (@additive_preadditive C Prod t Add) t (@additive_terminal_object C
  Prod t Add) P (@transf_arrow_diagram_func K C B X b)) (@finite_arrow_tail_next (Functor_cat K C)
  (@OneCatNativeExactArrowPair K C (@additive_preadditive C Prod t Add) C1 t (@additive_terminal_object C Prod t
  Add) T0 P Q N) (succ (succ (succ zero))) (@kernel_adjunction_family_func K C (@additive_preadditive C Prod t
  Add) t (@additive_terminal_object C Prod t Add) P (@one_cat_native_snake_alpha_diagram K C
  (@additive_preadditive C Prod t Add) C1 t (@additive_terminal_object C Prod t Add) T0 P A B X D b c h))
  (@kernel_adjunction_family_func K C (@additive_preadditive C Prod t Add) t (@additive_terminal_object C Prod t
  Add) P (@transf_arrow_diagram_func K C B X b)) (@one_cat_native_snake_kernel_first K C (@additive_preadditive
  C Prod t Add) C1 t (@additive_terminal_object C Prod t Add) T0 P Q A B X D b c h)
  (@one_cat_native_snake_six_term_result K C C1 Prod t Add T0 P Q N A B X D b c h)) (@finite_arrow_tail_arrow
  (Functor_cat K C) (@OneCatNativeExactArrowPair K C (@additive_preadditive C Prod t Add) C1 t
  (@additive_terminal_object C Prod t Add) T0 P Q N) (succ (succ (succ zero))) (@kernel_adjunction_family_func K
  C (@additive_preadditive C Prod t Add) t (@additive_terminal_object C Prod t Add) P
  (@one_cat_native_snake_alpha_diagram K C (@additive_preadditive C Prod t Add) C1 t (@additive_terminal_object
  C Prod t Add) T0 P A B X D b c h)) (@kernel_adjunction_family_func K C (@additive_preadditive C Prod t Add) t
  (@additive_terminal_object C Prod t Add) P (@transf_arrow_diagram_func K C B X b))
  (@one_cat_native_snake_kernel_first K C (@additive_preadditive C Prod t Add) C1 t (@additive_terminal_object C
  Prod t Add) T0 P Q A B X D b c h) (@one_cat_native_snake_six_term_result K C C1 Prod t Add T0 P Q N A B X D b
  c h)) (@finite_arrow_tail_rest (Functor_cat K C) (@OneCatNativeExactArrowPair K C (@additive_preadditive C
  Prod t Add) C1 t (@additive_terminal_object C Prod t Add) T0 P Q N) (succ (succ (succ zero)))
  (@kernel_adjunction_family_func K C (@additive_preadditive C Prod t Add) t (@additive_terminal_object C Prod t
  Add) P (@one_cat_native_snake_alpha_diagram K C (@additive_preadditive C Prod t Add) C1 t
  (@additive_terminal_object C Prod t Add) T0 P A B X D b c h)) (@kernel_adjunction_family_func K C
  (@additive_preadditive C Prod t Add) t (@additive_terminal_object C Prod t Add) P (@transf_arrow_diagram_func
  K C B X b)) (@one_cat_native_snake_kernel_first K C (@additive_preadditive C Prod t Add) C1 t
  (@additive_terminal_object C Prod t Add) T0 P Q A B X D b c h) (@one_cat_native_snake_six_term_result K C C1
  Prod t Add T0 P Q N A B X D b c h))) (@finite_arrow_tail_rest (Functor_cat K C) (@OneCatNativeExactArrowPair K
  C (@additive_preadditive C Prod t Add) C1 t (@additive_terminal_object C Prod t Add) T0 P Q N) (succ (succ
  zero)) (@kernel_adjunction_family_func K C (@additive_preadditive C Prod t Add) t (@additive_terminal_object C
  Prod t Add) P (@transf_arrow_diagram_func K C B X b)) (@finite_arrow_tail_next (Functor_cat K C)
  (@OneCatNativeExactArrowPair K C (@additive_preadditive C Prod t Add) C1 t (@additive_terminal_object C Prod t
  Add) T0 P Q N) (succ (succ (succ zero))) (@kernel_adjunction_family_func K C (@additive_preadditive C Prod t
  Add) t (@additive_terminal_object C Prod t Add) P (@one_cat_native_snake_alpha_diagram K C
  (@additive_preadditive C Prod t Add) C1 t (@additive_terminal_object C Prod t Add) T0 P A B X D b c h))
  (@kernel_adjunction_family_func K C (@additive_preadditive C Prod t Add) t (@additive_terminal_object C Prod t
  Add) P (@transf_arrow_diagram_func K C B X b)) (@one_cat_native_snake_kernel_first K C (@additive_preadditive
  C Prod t Add) C1 t (@additive_terminal_object C Prod t Add) T0 P Q A B X D b c h)
  (@one_cat_native_snake_six_term_result K C C1 Prod t Add T0 P Q N A B X D b c h)) (@finite_arrow_tail_arrow
  (Functor_cat K C) (@OneCatNativeExactArrowPair K C (@additive_preadditive C Prod t Add) C1 t
  (@additive_terminal_object C Prod t Add) T0 P Q N) (succ (succ (succ zero))) (@kernel_adjunction_family_func K
  C (@additive_preadditive C Prod t Add) t (@additive_terminal_object C Prod t Add) P
  (@one_cat_native_snake_alpha_diagram K C (@additive_preadditive C Prod t Add) C1 t (@additive_terminal_object
  C Prod t Add) T0 P A B X D b c h)) (@kernel_adjunction_family_func K C (@additive_preadditive C Prod t Add) t
  (@additive_terminal_object C Prod t Add) P (@transf_arrow_diagram_func K C B X b))
  (@one_cat_native_snake_kernel_first K C (@additive_preadditive C Prod t Add) C1 t (@additive_terminal_object C
  Prod t Add) T0 P Q A B X D b c h) (@one_cat_native_snake_six_term_result K C C1 Prod t Add T0 P Q N A B X D b
  c h)) (@finite_arrow_tail_rest (Functor_cat K C) (@OneCatNativeExactArrowPair K C (@additive_preadditive C
  Prod t Add) C1 t (@additive_terminal_object C Prod t Add) T0 P Q N) (succ (succ (succ zero)))
  (@kernel_adjunction_family_func K C (@additive_preadditive C Prod t Add) t (@additive_terminal_object C Prod t
  Add) P (@one_cat_native_snake_alpha_diagram K C (@additive_preadditive C Prod t Add) C1 t
  (@additive_terminal_object C Prod t Add) T0 P A B X D b c h)) (@kernel_adjunction_family_func K C
  (@additive_preadditive C Prod t Add) t (@additive_terminal_object C Prod t Add) P (@transf_arrow_diagram_func
  K C B X b)) (@one_cat_native_snake_kernel_first K C (@additive_preadditive C Prod t Add) C1 t
  (@additive_terminal_object C Prod t Add) T0 P Q A B X D b c h) (@one_cat_native_snake_six_term_result K C C1
  Prod t Add T0 P Q N A B X D b c h)))) (@finite_arrow_tail_rest (Functor_cat K C) (@OneCatNativeExactArrowPair
  K C (@additive_preadditive C Prod t Add) C1 t (@additive_terminal_object C Prod t Add) T0 P Q N) (succ zero)
  (@finite_arrow_tail_next (Functor_cat K C) (@OneCatNativeExactArrowPair K C (@additive_preadditive C Prod t
  Add) C1 t (@additive_terminal_object C Prod t Add) T0 P Q N) (succ (succ (succ zero)))
  (@kernel_adjunction_family_func K C (@additive_preadditive C Prod t Add) t (@additive_terminal_object C Prod t
  Add) P (@one_cat_native_snake_alpha_diagram K C (@additive_preadditive C Prod t Add) C1 t
  (@additive_terminal_object C Prod t Add) T0 P A B X D b c h)) (@kernel_adjunction_family_func K C
  (@additive_preadditive C Prod t Add) t (@additive_terminal_object C Prod t Add) P (@transf_arrow_diagram_func
  K C B X b)) (@one_cat_native_snake_kernel_first K C (@additive_preadditive C Prod t Add) C1 t
  (@additive_terminal_object C Prod t Add) T0 P Q A B X D b c h) (@one_cat_native_snake_six_term_result K C C1
  Prod t Add T0 P Q N A B X D b c h)) (@finite_arrow_tail_next (Functor_cat K C) (@OneCatNativeExactArrowPair K
  C (@additive_preadditive C Prod t Add) C1 t (@additive_terminal_object C Prod t Add) T0 P Q N) (succ (succ
  zero)) (@kernel_adjunction_family_func K C (@additive_preadditive C Prod t Add) t (@additive_terminal_object C
  Prod t Add) P (@transf_arrow_diagram_func K C B X b)) (@finite_arrow_tail_next (Functor_cat K C)
  (@OneCatNativeExactArrowPair K C (@additive_preadditive C Prod t Add) C1 t (@additive_terminal_object C Prod t
  Add) T0 P Q N) (succ (succ (succ zero))) (@kernel_adjunction_family_func K C (@additive_preadditive C Prod t
  Add) t (@additive_terminal_object C Prod t Add) P (@one_cat_native_snake_alpha_diagram K C
  (@additive_preadditive C Prod t Add) C1 t (@additive_terminal_object C Prod t Add) T0 P A B X D b c h))
  (@kernel_adjunction_family_func K C (@additive_preadditive C Prod t Add) t (@additive_terminal_object C Prod t
  Add) P (@transf_arrow_diagram_func K C B X b)) (@one_cat_native_snake_kernel_first K C (@additive_preadditive
  C Prod t Add) C1 t (@additive_terminal_object C Prod t Add) T0 P Q A B X D b c h)
  (@one_cat_native_snake_six_term_result K C C1 Prod t Add T0 P Q N A B X D b c h)) (@finite_arrow_tail_arrow
  (Functor_cat K C) (@OneCatNativeExactArrowPair K C (@additive_preadditive C Prod t Add) C1 t
  (@additive_terminal_object C Prod t Add) T0 P Q N) (succ (succ (succ zero))) (@kernel_adjunction_family_func K
  C (@additive_preadditive C Prod t Add) t (@additive_terminal_object C Prod t Add) P
  (@one_cat_native_snake_alpha_diagram K C (@additive_preadditive C Prod t Add) C1 t (@additive_terminal_object
  C Prod t Add) T0 P A B X D b c h)) (@kernel_adjunction_family_func K C (@additive_preadditive C Prod t Add) t
  (@additive_terminal_object C Prod t Add) P (@transf_arrow_diagram_func K C B X b))
  (@one_cat_native_snake_kernel_first K C (@additive_preadditive C Prod t Add) C1 t (@additive_terminal_object C
  Prod t Add) T0 P Q A B X D b c h) (@one_cat_native_snake_six_term_result K C C1 Prod t Add T0 P Q N A B X D b
  c h)) (@finite_arrow_tail_rest (Functor_cat K C) (@OneCatNativeExactArrowPair K C (@additive_preadditive C
  Prod t Add) C1 t (@additive_terminal_object C Prod t Add) T0 P Q N) (succ (succ (succ zero)))
  (@kernel_adjunction_family_func K C (@additive_preadditive C Prod t Add) t (@additive_terminal_object C Prod t
  Add) P (@one_cat_native_snake_alpha_diagram K C (@additive_preadditive C Prod t Add) C1 t
  (@additive_terminal_object C Prod t Add) T0 P A B X D b c h)) (@kernel_adjunction_family_func K C
  (@additive_preadditive C Prod t Add) t (@additive_terminal_object C Prod t Add) P (@transf_arrow_diagram_func
  K C B X b)) (@one_cat_native_snake_kernel_first K C (@additive_preadditive C Prod t Add) C1 t
  (@additive_terminal_object C Prod t Add) T0 P Q A B X D b c h) (@one_cat_native_snake_six_term_result K C C1
  Prod t Add T0 P Q N A B X D b c h))) (@finite_arrow_tail_arrow (Functor_cat K C) (@OneCatNativeExactArrowPair
  K C (@additive_preadditive C Prod t Add) C1 t (@additive_terminal_object C Prod t Add) T0 P Q N) (succ (succ
  zero)) (@kernel_adjunction_family_func K C (@additive_preadditive C Prod t Add) t (@additive_terminal_object C
  Prod t Add) P (@transf_arrow_diagram_func K C B X b)) (@finite_arrow_tail_next (Functor_cat K C)
  (@OneCatNativeExactArrowPair K C (@additive_preadditive C Prod t Add) C1 t (@additive_terminal_object C Prod t
  Add) T0 P Q N) (succ (succ (succ zero))) (@kernel_adjunction_family_func K C (@additive_preadditive C Prod t
  Add) t (@additive_terminal_object C Prod t Add) P (@one_cat_native_snake_alpha_diagram K C
  (@additive_preadditive C Prod t Add) C1 t (@additive_terminal_object C Prod t Add) T0 P A B X D b c h))
  (@kernel_adjunction_family_func K C (@additive_preadditive C Prod t Add) t (@additive_terminal_object C Prod t
  Add) P (@transf_arrow_diagram_func K C B X b)) (@one_cat_native_snake_kernel_first K C (@additive_preadditive
  C Prod t Add) C1 t (@additive_terminal_object C Prod t Add) T0 P Q A B X D b c h)
  (@one_cat_native_snake_six_term_result K C C1 Prod t Add T0 P Q N A B X D b c h)) (@finite_arrow_tail_arrow
  (Functor_cat K C) (@OneCatNativeExactArrowPair K C (@additive_preadditive C Prod t Add) C1 t
  (@additive_terminal_object C Prod t Add) T0 P Q N) (succ (succ (succ zero))) (@kernel_adjunction_family_func K
  C (@additive_preadditive C Prod t Add) t (@additive_terminal_object C Prod t Add) P
  (@one_cat_native_snake_alpha_diagram K C (@additive_preadditive C Prod t Add) C1 t (@additive_terminal_object
  C Prod t Add) T0 P A B X D b c h)) (@kernel_adjunction_family_func K C (@additive_preadditive C Prod t Add) t
  (@additive_terminal_object C Prod t Add) P (@transf_arrow_diagram_func K C B X b))
  (@one_cat_native_snake_kernel_first K C (@additive_preadditive C Prod t Add) C1 t (@additive_terminal_object C
  Prod t Add) T0 P Q A B X D b c h) (@one_cat_native_snake_six_term_result K C C1 Prod t Add T0 P Q N A B X D b
  c h)) (@finite_arrow_tail_rest (Functor_cat K C) (@OneCatNativeExactArrowPair K C (@additive_preadditive C
  Prod t Add) C1 t (@additive_terminal_object C Prod t Add) T0 P Q N) (succ (succ (succ zero)))
  (@kernel_adjunction_family_func K C (@additive_preadditive C Prod t Add) t (@additive_terminal_object C Prod t
  Add) P (@one_cat_native_snake_alpha_diagram K C (@additive_preadditive C Prod t Add) C1 t
  (@additive_terminal_object C Prod t Add) T0 P A B X D b c h)) (@kernel_adjunction_family_func K C
  (@additive_preadditive C Prod t Add) t (@additive_terminal_object C Prod t Add) P (@transf_arrow_diagram_func
  K C B X b)) (@one_cat_native_snake_kernel_first K C (@additive_preadditive C Prod t Add) C1 t
  (@additive_terminal_object C Prod t Add) T0 P Q A B X D b c h) (@one_cat_native_snake_six_term_result K C C1
  Prod t Add T0 P Q N A B X D b c h))) (@finite_arrow_tail_rest (Functor_cat K C) (@OneCatNativeExactArrowPair K
  C (@additive_preadditive C Prod t Add) C1 t (@additive_terminal_object C Prod t Add) T0 P Q N) (succ (succ
  zero)) (@kernel_adjunction_family_func K C (@additive_preadditive C Prod t Add) t (@additive_terminal_object C
  Prod t Add) P (@transf_arrow_diagram_func K C B X b)) (@finite_arrow_tail_next (Functor_cat K C)
  (@OneCatNativeExactArrowPair K C (@additive_preadditive C Prod t Add) C1 t (@additive_terminal_object C Prod t
  Add) T0 P Q N) (succ (succ (succ zero))) (@kernel_adjunction_family_func K C (@additive_preadditive C Prod t
  Add) t (@additive_terminal_object C Prod t Add) P (@one_cat_native_snake_alpha_diagram K C
  (@additive_preadditive C Prod t Add) C1 t (@additive_terminal_object C Prod t Add) T0 P A B X D b c h))
  (@kernel_adjunction_family_func K C (@additive_preadditive C Prod t Add) t (@additive_terminal_object C Prod t
  Add) P (@transf_arrow_diagram_func K C B X b)) (@one_cat_native_snake_kernel_first K C (@additive_preadditive
  C Prod t Add) C1 t (@additive_terminal_object C Prod t Add) T0 P Q A B X D b c h)
  (@one_cat_native_snake_six_term_result K C C1 Prod t Add T0 P Q N A B X D b c h)) (@finite_arrow_tail_arrow
  (Functor_cat K C) (@OneCatNativeExactArrowPair K C (@additive_preadditive C Prod t Add) C1 t
  (@additive_terminal_object C Prod t Add) T0 P Q N) (succ (succ (succ zero))) (@kernel_adjunction_family_func K
  C (@additive_preadditive C Prod t Add) t (@additive_terminal_object C Prod t Add) P
  (@one_cat_native_snake_alpha_diagram K C (@additive_preadditive C Prod t Add) C1 t (@additive_terminal_object
  C Prod t Add) T0 P A B X D b c h)) (@kernel_adjunction_family_func K C (@additive_preadditive C Prod t Add) t
  (@additive_terminal_object C Prod t Add) P (@transf_arrow_diagram_func K C B X b))
  (@one_cat_native_snake_kernel_first K C (@additive_preadditive C Prod t Add) C1 t (@additive_terminal_object C
  Prod t Add) T0 P Q A B X D b c h) (@one_cat_native_snake_six_term_result K C C1 Prod t Add T0 P Q N A B X D b
  c h)) (@finite_arrow_tail_rest (Functor_cat K C) (@OneCatNativeExactArrowPair K C (@additive_preadditive C
  Prod t Add) C1 t (@additive_terminal_object C Prod t Add) T0 P Q N) (succ (succ (succ zero)))
  (@kernel_adjunction_family_func K C (@additive_preadditive C Prod t Add) t (@additive_terminal_object C Prod t
  Add) P (@one_cat_native_snake_alpha_diagram K C (@additive_preadditive C Prod t Add) C1 t
  (@additive_terminal_object C Prod t Add) T0 P A B X D b c h)) (@kernel_adjunction_family_func K C
  (@additive_preadditive C Prod t Add) t (@additive_terminal_object C Prod t Add) P (@transf_arrow_diagram_func
  K C B X b)) (@one_cat_native_snake_kernel_first K C (@additive_preadditive C Prod t Add) C1 t
  (@additive_terminal_object C Prod t Add) T0 P Q A B X D b c h) (@one_cat_native_snake_six_term_result K C C1
  Prod t Add T0 P Q N A B X D b c h)))))) ≡ (@one_cat_native_snake_fourth_exact_input K C C1 Prod t Add T0 P Q N
  A B X D b c h);

// The actual stored pair has its derived whole zero composite.
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
  ⊢ (@one_cat_native_exact_arrow_pair_zero K C (@additive_preadditive C Prod t Add) C1 t
  (@additive_terminal_object C Prod t Add) T0 P Q N (@finite_arrow_tail_next (Functor_cat K C)
  (@OneCatNativeExactArrowPair K C (@additive_preadditive C Prod t Add) C1 t (@additive_terminal_object C Prod t
  Add) T0 P Q N) (succ (succ zero)) (@kernel_adjunction_family_func K C (@additive_preadditive C Prod t Add) t
  (@additive_terminal_object C Prod t Add) P (@transf_arrow_diagram_func K C B X b)) (@finite_arrow_tail_next
  (Functor_cat K C) (@OneCatNativeExactArrowPair K C (@additive_preadditive C Prod t Add) C1 t
  (@additive_terminal_object C Prod t Add) T0 P Q N) (succ (succ (succ zero))) (@kernel_adjunction_family_func K
  C (@additive_preadditive C Prod t Add) t (@additive_terminal_object C Prod t Add) P
  (@one_cat_native_snake_alpha_diagram K C (@additive_preadditive C Prod t Add) C1 t (@additive_terminal_object
  C Prod t Add) T0 P A B X D b c h)) (@kernel_adjunction_family_func K C (@additive_preadditive C Prod t Add) t
  (@additive_terminal_object C Prod t Add) P (@transf_arrow_diagram_func K C B X b))
  (@one_cat_native_snake_kernel_first K C (@additive_preadditive C Prod t Add) C1 t (@additive_terminal_object C
  Prod t Add) T0 P Q A B X D b c h) (@one_cat_native_snake_six_term_result K C C1 Prod t Add T0 P Q N A B X D b
  c h)) (@finite_arrow_tail_arrow (Functor_cat K C) (@OneCatNativeExactArrowPair K C (@additive_preadditive C
  Prod t Add) C1 t (@additive_terminal_object C Prod t Add) T0 P Q N) (succ (succ (succ zero)))
  (@kernel_adjunction_family_func K C (@additive_preadditive C Prod t Add) t (@additive_terminal_object C Prod t
  Add) P (@one_cat_native_snake_alpha_diagram K C (@additive_preadditive C Prod t Add) C1 t
  (@additive_terminal_object C Prod t Add) T0 P A B X D b c h)) (@kernel_adjunction_family_func K C
  (@additive_preadditive C Prod t Add) t (@additive_terminal_object C Prod t Add) P (@transf_arrow_diagram_func
  K C B X b)) (@one_cat_native_snake_kernel_first K C (@additive_preadditive C Prod t Add) C1 t
  (@additive_terminal_object C Prod t Add) T0 P Q A B X D b c h) (@one_cat_native_snake_six_term_result K C C1
  Prod t Add T0 P Q N A B X D b c h)) (@finite_arrow_tail_rest (Functor_cat K C) (@OneCatNativeExactArrowPair K
  C (@additive_preadditive C Prod t Add) C1 t (@additive_terminal_object C Prod t Add) T0 P Q N) (succ (succ
  (succ zero))) (@kernel_adjunction_family_func K C (@additive_preadditive C Prod t Add) t
  (@additive_terminal_object C Prod t Add) P (@one_cat_native_snake_alpha_diagram K C (@additive_preadditive C
  Prod t Add) C1 t (@additive_terminal_object C Prod t Add) T0 P A B X D b c h)) (@kernel_adjunction_family_func
  K C (@additive_preadditive C Prod t Add) t (@additive_terminal_object C Prod t Add) P
  (@transf_arrow_diagram_func K C B X b)) (@one_cat_native_snake_kernel_first K C (@additive_preadditive C Prod
  t Add) C1 t (@additive_terminal_object C Prod t Add) T0 P Q A B X D b c h)
  (@one_cat_native_snake_six_term_result K C C1 Prod t Add T0 P Q N A B X D b c h))) (@finite_arrow_tail_next
  (Functor_cat K C) (@OneCatNativeExactArrowPair K C (@additive_preadditive C Prod t Add) C1 t
  (@additive_terminal_object C Prod t Add) T0 P Q N) (succ zero) (@finite_arrow_tail_next (Functor_cat K C)
  (@OneCatNativeExactArrowPair K C (@additive_preadditive C Prod t Add) C1 t (@additive_terminal_object C Prod t
  Add) T0 P Q N) (succ (succ (succ zero))) (@kernel_adjunction_family_func K C (@additive_preadditive C Prod t
  Add) t (@additive_terminal_object C Prod t Add) P (@one_cat_native_snake_alpha_diagram K C
  (@additive_preadditive C Prod t Add) C1 t (@additive_terminal_object C Prod t Add) T0 P A B X D b c h))
  (@kernel_adjunction_family_func K C (@additive_preadditive C Prod t Add) t (@additive_terminal_object C Prod t
  Add) P (@transf_arrow_diagram_func K C B X b)) (@one_cat_native_snake_kernel_first K C (@additive_preadditive
  C Prod t Add) C1 t (@additive_terminal_object C Prod t Add) T0 P Q A B X D b c h)
  (@one_cat_native_snake_six_term_result K C C1 Prod t Add T0 P Q N A B X D b c h)) (@finite_arrow_tail_next
  (Functor_cat K C) (@OneCatNativeExactArrowPair K C (@additive_preadditive C Prod t Add) C1 t
  (@additive_terminal_object C Prod t Add) T0 P Q N) (succ (succ zero)) (@kernel_adjunction_family_func K C
  (@additive_preadditive C Prod t Add) t (@additive_terminal_object C Prod t Add) P (@transf_arrow_diagram_func
  K C B X b)) (@finite_arrow_tail_next (Functor_cat K C) (@OneCatNativeExactArrowPair K C (@additive_preadditive
  C Prod t Add) C1 t (@additive_terminal_object C Prod t Add) T0 P Q N) (succ (succ (succ zero)))
  (@kernel_adjunction_family_func K C (@additive_preadditive C Prod t Add) t (@additive_terminal_object C Prod t
  Add) P (@one_cat_native_snake_alpha_diagram K C (@additive_preadditive C Prod t Add) C1 t
  (@additive_terminal_object C Prod t Add) T0 P A B X D b c h)) (@kernel_adjunction_family_func K C
  (@additive_preadditive C Prod t Add) t (@additive_terminal_object C Prod t Add) P (@transf_arrow_diagram_func
  K C B X b)) (@one_cat_native_snake_kernel_first K C (@additive_preadditive C Prod t Add) C1 t
  (@additive_terminal_object C Prod t Add) T0 P Q A B X D b c h) (@one_cat_native_snake_six_term_result K C C1
  Prod t Add T0 P Q N A B X D b c h)) (@finite_arrow_tail_arrow (Functor_cat K C) (@OneCatNativeExactArrowPair K
  C (@additive_preadditive C Prod t Add) C1 t (@additive_terminal_object C Prod t Add) T0 P Q N) (succ (succ
  (succ zero))) (@kernel_adjunction_family_func K C (@additive_preadditive C Prod t Add) t
  (@additive_terminal_object C Prod t Add) P (@one_cat_native_snake_alpha_diagram K C (@additive_preadditive C
  Prod t Add) C1 t (@additive_terminal_object C Prod t Add) T0 P A B X D b c h)) (@kernel_adjunction_family_func
  K C (@additive_preadditive C Prod t Add) t (@additive_terminal_object C Prod t Add) P
  (@transf_arrow_diagram_func K C B X b)) (@one_cat_native_snake_kernel_first K C (@additive_preadditive C Prod
  t Add) C1 t (@additive_terminal_object C Prod t Add) T0 P Q A B X D b c h)
  (@one_cat_native_snake_six_term_result K C C1 Prod t Add T0 P Q N A B X D b c h)) (@finite_arrow_tail_rest
  (Functor_cat K C) (@OneCatNativeExactArrowPair K C (@additive_preadditive C Prod t Add) C1 t
  (@additive_terminal_object C Prod t Add) T0 P Q N) (succ (succ (succ zero))) (@kernel_adjunction_family_func K
  C (@additive_preadditive C Prod t Add) t (@additive_terminal_object C Prod t Add) P
  (@one_cat_native_snake_alpha_diagram K C (@additive_preadditive C Prod t Add) C1 t (@additive_terminal_object
  C Prod t Add) T0 P A B X D b c h)) (@kernel_adjunction_family_func K C (@additive_preadditive C Prod t Add) t
  (@additive_terminal_object C Prod t Add) P (@transf_arrow_diagram_func K C B X b))
  (@one_cat_native_snake_kernel_first K C (@additive_preadditive C Prod t Add) C1 t (@additive_terminal_object C
  Prod t Add) T0 P Q A B X D b c h) (@one_cat_native_snake_six_term_result K C C1 Prod t Add T0 P Q N A B X D b
  c h))) (@finite_arrow_tail_arrow (Functor_cat K C) (@OneCatNativeExactArrowPair K C (@additive_preadditive C
  Prod t Add) C1 t (@additive_terminal_object C Prod t Add) T0 P Q N) (succ (succ zero))
  (@kernel_adjunction_family_func K C (@additive_preadditive C Prod t Add) t (@additive_terminal_object C Prod t
  Add) P (@transf_arrow_diagram_func K C B X b)) (@finite_arrow_tail_next (Functor_cat K C)
  (@OneCatNativeExactArrowPair K C (@additive_preadditive C Prod t Add) C1 t (@additive_terminal_object C Prod t
  Add) T0 P Q N) (succ (succ (succ zero))) (@kernel_adjunction_family_func K C (@additive_preadditive C Prod t
  Add) t (@additive_terminal_object C Prod t Add) P (@one_cat_native_snake_alpha_diagram K C
  (@additive_preadditive C Prod t Add) C1 t (@additive_terminal_object C Prod t Add) T0 P A B X D b c h))
  (@kernel_adjunction_family_func K C (@additive_preadditive C Prod t Add) t (@additive_terminal_object C Prod t
  Add) P (@transf_arrow_diagram_func K C B X b)) (@one_cat_native_snake_kernel_first K C (@additive_preadditive
  C Prod t Add) C1 t (@additive_terminal_object C Prod t Add) T0 P Q A B X D b c h)
  (@one_cat_native_snake_six_term_result K C C1 Prod t Add T0 P Q N A B X D b c h)) (@finite_arrow_tail_arrow
  (Functor_cat K C) (@OneCatNativeExactArrowPair K C (@additive_preadditive C Prod t Add) C1 t
  (@additive_terminal_object C Prod t Add) T0 P Q N) (succ (succ (succ zero))) (@kernel_adjunction_family_func K
  C (@additive_preadditive C Prod t Add) t (@additive_terminal_object C Prod t Add) P
  (@one_cat_native_snake_alpha_diagram K C (@additive_preadditive C Prod t Add) C1 t (@additive_terminal_object
  C Prod t Add) T0 P A B X D b c h)) (@kernel_adjunction_family_func K C (@additive_preadditive C Prod t Add) t
  (@additive_terminal_object C Prod t Add) P (@transf_arrow_diagram_func K C B X b))
  (@one_cat_native_snake_kernel_first K C (@additive_preadditive C Prod t Add) C1 t (@additive_terminal_object C
  Prod t Add) T0 P Q A B X D b c h) (@one_cat_native_snake_six_term_result K C C1 Prod t Add T0 P Q N A B X D b
  c h)) (@finite_arrow_tail_rest (Functor_cat K C) (@OneCatNativeExactArrowPair K C (@additive_preadditive C
  Prod t Add) C1 t (@additive_terminal_object C Prod t Add) T0 P Q N) (succ (succ (succ zero)))
  (@kernel_adjunction_family_func K C (@additive_preadditive C Prod t Add) t (@additive_terminal_object C Prod t
  Add) P (@one_cat_native_snake_alpha_diagram K C (@additive_preadditive C Prod t Add) C1 t
  (@additive_terminal_object C Prod t Add) T0 P A B X D b c h)) (@kernel_adjunction_family_func K C
  (@additive_preadditive C Prod t Add) t (@additive_terminal_object C Prod t Add) P (@transf_arrow_diagram_func
  K C B X b)) (@one_cat_native_snake_kernel_first K C (@additive_preadditive C Prod t Add) C1 t
  (@additive_terminal_object C Prod t Add) T0 P Q A B X D b c h) (@one_cat_native_snake_six_term_result K C C1
  Prod t Add T0 P Q N A B X D b c h))) (@finite_arrow_tail_rest (Functor_cat K C) (@OneCatNativeExactArrowPair K
  C (@additive_preadditive C Prod t Add) C1 t (@additive_terminal_object C Prod t Add) T0 P Q N) (succ (succ
  zero)) (@kernel_adjunction_family_func K C (@additive_preadditive C Prod t Add) t (@additive_terminal_object C
  Prod t Add) P (@transf_arrow_diagram_func K C B X b)) (@finite_arrow_tail_next (Functor_cat K C)
  (@OneCatNativeExactArrowPair K C (@additive_preadditive C Prod t Add) C1 t (@additive_terminal_object C Prod t
  Add) T0 P Q N) (succ (succ (succ zero))) (@kernel_adjunction_family_func K C (@additive_preadditive C Prod t
  Add) t (@additive_terminal_object C Prod t Add) P (@one_cat_native_snake_alpha_diagram K C
  (@additive_preadditive C Prod t Add) C1 t (@additive_terminal_object C Prod t Add) T0 P A B X D b c h))
  (@kernel_adjunction_family_func K C (@additive_preadditive C Prod t Add) t (@additive_terminal_object C Prod t
  Add) P (@transf_arrow_diagram_func K C B X b)) (@one_cat_native_snake_kernel_first K C (@additive_preadditive
  C Prod t Add) C1 t (@additive_terminal_object C Prod t Add) T0 P Q A B X D b c h)
  (@one_cat_native_snake_six_term_result K C C1 Prod t Add T0 P Q N A B X D b c h)) (@finite_arrow_tail_arrow
  (Functor_cat K C) (@OneCatNativeExactArrowPair K C (@additive_preadditive C Prod t Add) C1 t
  (@additive_terminal_object C Prod t Add) T0 P Q N) (succ (succ (succ zero))) (@kernel_adjunction_family_func K
  C (@additive_preadditive C Prod t Add) t (@additive_terminal_object C Prod t Add) P
  (@one_cat_native_snake_alpha_diagram K C (@additive_preadditive C Prod t Add) C1 t (@additive_terminal_object
  C Prod t Add) T0 P A B X D b c h)) (@kernel_adjunction_family_func K C (@additive_preadditive C Prod t Add) t
  (@additive_terminal_object C Prod t Add) P (@transf_arrow_diagram_func K C B X b))
  (@one_cat_native_snake_kernel_first K C (@additive_preadditive C Prod t Add) C1 t (@additive_terminal_object C
  Prod t Add) T0 P Q A B X D b c h) (@one_cat_native_snake_six_term_result K C C1 Prod t Add T0 P Q N A B X D b
  c h)) (@finite_arrow_tail_rest (Functor_cat K C) (@OneCatNativeExactArrowPair K C (@additive_preadditive C
  Prod t Add) C1 t (@additive_terminal_object C Prod t Add) T0 P Q N) (succ (succ (succ zero)))
  (@kernel_adjunction_family_func K C (@additive_preadditive C Prod t Add) t (@additive_terminal_object C Prod t
  Add) P (@one_cat_native_snake_alpha_diagram K C (@additive_preadditive C Prod t Add) C1 t
  (@additive_terminal_object C Prod t Add) T0 P A B X D b c h)) (@kernel_adjunction_family_func K C
  (@additive_preadditive C Prod t Add) t (@additive_terminal_object C Prod t Add) P (@transf_arrow_diagram_func
  K C B X b)) (@one_cat_native_snake_kernel_first K C (@additive_preadditive C Prod t Add) C1 t
  (@additive_terminal_object C Prod t Add) T0 P Q A B X D b c h) (@one_cat_native_snake_six_term_result K C C1
  Prod t Add T0 P Q N A B X D b c h)))) (@finite_arrow_tail_next (Functor_cat K C) (@OneCatNativeExactArrowPair
  K C (@additive_preadditive C Prod t Add) C1 t (@additive_terminal_object C Prod t Add) T0 P Q N) zero
  (@finite_arrow_tail_next (Functor_cat K C) (@OneCatNativeExactArrowPair K C (@additive_preadditive C Prod t
  Add) C1 t (@additive_terminal_object C Prod t Add) T0 P Q N) (succ (succ zero))
  (@kernel_adjunction_family_func K C (@additive_preadditive C Prod t Add) t (@additive_terminal_object C Prod t
  Add) P (@transf_arrow_diagram_func K C B X b)) (@finite_arrow_tail_next (Functor_cat K C)
  (@OneCatNativeExactArrowPair K C (@additive_preadditive C Prod t Add) C1 t (@additive_terminal_object C Prod t
  Add) T0 P Q N) (succ (succ (succ zero))) (@kernel_adjunction_family_func K C (@additive_preadditive C Prod t
  Add) t (@additive_terminal_object C Prod t Add) P (@one_cat_native_snake_alpha_diagram K C
  (@additive_preadditive C Prod t Add) C1 t (@additive_terminal_object C Prod t Add) T0 P A B X D b c h))
  (@kernel_adjunction_family_func K C (@additive_preadditive C Prod t Add) t (@additive_terminal_object C Prod t
  Add) P (@transf_arrow_diagram_func K C B X b)) (@one_cat_native_snake_kernel_first K C (@additive_preadditive
  C Prod t Add) C1 t (@additive_terminal_object C Prod t Add) T0 P Q A B X D b c h)
  (@one_cat_native_snake_six_term_result K C C1 Prod t Add T0 P Q N A B X D b c h)) (@finite_arrow_tail_arrow
  (Functor_cat K C) (@OneCatNativeExactArrowPair K C (@additive_preadditive C Prod t Add) C1 t
  (@additive_terminal_object C Prod t Add) T0 P Q N) (succ (succ (succ zero))) (@kernel_adjunction_family_func K
  C (@additive_preadditive C Prod t Add) t (@additive_terminal_object C Prod t Add) P
  (@one_cat_native_snake_alpha_diagram K C (@additive_preadditive C Prod t Add) C1 t (@additive_terminal_object
  C Prod t Add) T0 P A B X D b c h)) (@kernel_adjunction_family_func K C (@additive_preadditive C Prod t Add) t
  (@additive_terminal_object C Prod t Add) P (@transf_arrow_diagram_func K C B X b))
  (@one_cat_native_snake_kernel_first K C (@additive_preadditive C Prod t Add) C1 t (@additive_terminal_object C
  Prod t Add) T0 P Q A B X D b c h) (@one_cat_native_snake_six_term_result K C C1 Prod t Add T0 P Q N A B X D b
  c h)) (@finite_arrow_tail_rest (Functor_cat K C) (@OneCatNativeExactArrowPair K C (@additive_preadditive C
  Prod t Add) C1 t (@additive_terminal_object C Prod t Add) T0 P Q N) (succ (succ (succ zero)))
  (@kernel_adjunction_family_func K C (@additive_preadditive C Prod t Add) t (@additive_terminal_object C Prod t
  Add) P (@one_cat_native_snake_alpha_diagram K C (@additive_preadditive C Prod t Add) C1 t
  (@additive_terminal_object C Prod t Add) T0 P A B X D b c h)) (@kernel_adjunction_family_func K C
  (@additive_preadditive C Prod t Add) t (@additive_terminal_object C Prod t Add) P (@transf_arrow_diagram_func
  K C B X b)) (@one_cat_native_snake_kernel_first K C (@additive_preadditive C Prod t Add) C1 t
  (@additive_terminal_object C Prod t Add) T0 P Q A B X D b c h) (@one_cat_native_snake_six_term_result K C C1
  Prod t Add T0 P Q N A B X D b c h))) (@finite_arrow_tail_next (Functor_cat K C) (@OneCatNativeExactArrowPair K
  C (@additive_preadditive C Prod t Add) C1 t (@additive_terminal_object C Prod t Add) T0 P Q N) (succ zero)
  (@finite_arrow_tail_next (Functor_cat K C) (@OneCatNativeExactArrowPair K C (@additive_preadditive C Prod t
  Add) C1 t (@additive_terminal_object C Prod t Add) T0 P Q N) (succ (succ (succ zero)))
  (@kernel_adjunction_family_func K C (@additive_preadditive C Prod t Add) t (@additive_terminal_object C Prod t
  Add) P (@one_cat_native_snake_alpha_diagram K C (@additive_preadditive C Prod t Add) C1 t
  (@additive_terminal_object C Prod t Add) T0 P A B X D b c h)) (@kernel_adjunction_family_func K C
  (@additive_preadditive C Prod t Add) t (@additive_terminal_object C Prod t Add) P (@transf_arrow_diagram_func
  K C B X b)) (@one_cat_native_snake_kernel_first K C (@additive_preadditive C Prod t Add) C1 t
  (@additive_terminal_object C Prod t Add) T0 P Q A B X D b c h) (@one_cat_native_snake_six_term_result K C C1
  Prod t Add T0 P Q N A B X D b c h)) (@finite_arrow_tail_next (Functor_cat K C) (@OneCatNativeExactArrowPair K
  C (@additive_preadditive C Prod t Add) C1 t (@additive_terminal_object C Prod t Add) T0 P Q N) (succ (succ
  zero)) (@kernel_adjunction_family_func K C (@additive_preadditive C Prod t Add) t (@additive_terminal_object C
  Prod t Add) P (@transf_arrow_diagram_func K C B X b)) (@finite_arrow_tail_next (Functor_cat K C)
  (@OneCatNativeExactArrowPair K C (@additive_preadditive C Prod t Add) C1 t (@additive_terminal_object C Prod t
  Add) T0 P Q N) (succ (succ (succ zero))) (@kernel_adjunction_family_func K C (@additive_preadditive C Prod t
  Add) t (@additive_terminal_object C Prod t Add) P (@one_cat_native_snake_alpha_diagram K C
  (@additive_preadditive C Prod t Add) C1 t (@additive_terminal_object C Prod t Add) T0 P A B X D b c h))
  (@kernel_adjunction_family_func K C (@additive_preadditive C Prod t Add) t (@additive_terminal_object C Prod t
  Add) P (@transf_arrow_diagram_func K C B X b)) (@one_cat_native_snake_kernel_first K C (@additive_preadditive
  C Prod t Add) C1 t (@additive_terminal_object C Prod t Add) T0 P Q A B X D b c h)
  (@one_cat_native_snake_six_term_result K C C1 Prod t Add T0 P Q N A B X D b c h)) (@finite_arrow_tail_arrow
  (Functor_cat K C) (@OneCatNativeExactArrowPair K C (@additive_preadditive C Prod t Add) C1 t
  (@additive_terminal_object C Prod t Add) T0 P Q N) (succ (succ (succ zero))) (@kernel_adjunction_family_func K
  C (@additive_preadditive C Prod t Add) t (@additive_terminal_object C Prod t Add) P
  (@one_cat_native_snake_alpha_diagram K C (@additive_preadditive C Prod t Add) C1 t (@additive_terminal_object
  C Prod t Add) T0 P A B X D b c h)) (@kernel_adjunction_family_func K C (@additive_preadditive C Prod t Add) t
  (@additive_terminal_object C Prod t Add) P (@transf_arrow_diagram_func K C B X b))
  (@one_cat_native_snake_kernel_first K C (@additive_preadditive C Prod t Add) C1 t (@additive_terminal_object C
  Prod t Add) T0 P Q A B X D b c h) (@one_cat_native_snake_six_term_result K C C1 Prod t Add T0 P Q N A B X D b
  c h)) (@finite_arrow_tail_rest (Functor_cat K C) (@OneCatNativeExactArrowPair K C (@additive_preadditive C
  Prod t Add) C1 t (@additive_terminal_object C Prod t Add) T0 P Q N) (succ (succ (succ zero)))
  (@kernel_adjunction_family_func K C (@additive_preadditive C Prod t Add) t (@additive_terminal_object C Prod t
  Add) P (@one_cat_native_snake_alpha_diagram K C (@additive_preadditive C Prod t Add) C1 t
  (@additive_terminal_object C Prod t Add) T0 P A B X D b c h)) (@kernel_adjunction_family_func K C
  (@additive_preadditive C Prod t Add) t (@additive_terminal_object C Prod t Add) P (@transf_arrow_diagram_func
  K C B X b)) (@one_cat_native_snake_kernel_first K C (@additive_preadditive C Prod t Add) C1 t
  (@additive_terminal_object C Prod t Add) T0 P Q A B X D b c h) (@one_cat_native_snake_six_term_result K C C1
  Prod t Add T0 P Q N A B X D b c h))) (@finite_arrow_tail_arrow (Functor_cat K C) (@OneCatNativeExactArrowPair
  K C (@additive_preadditive C Prod t Add) C1 t (@additive_terminal_object C Prod t Add) T0 P Q N) (succ (succ
  zero)) (@kernel_adjunction_family_func K C (@additive_preadditive C Prod t Add) t (@additive_terminal_object C
  Prod t Add) P (@transf_arrow_diagram_func K C B X b)) (@finite_arrow_tail_next (Functor_cat K C)
  (@OneCatNativeExactArrowPair K C (@additive_preadditive C Prod t Add) C1 t (@additive_terminal_object C Prod t
  Add) T0 P Q N) (succ (succ (succ zero))) (@kernel_adjunction_family_func K C (@additive_preadditive C Prod t
  Add) t (@additive_terminal_object C Prod t Add) P (@one_cat_native_snake_alpha_diagram K C
  (@additive_preadditive C Prod t Add) C1 t (@additive_terminal_object C Prod t Add) T0 P A B X D b c h))
  (@kernel_adjunction_family_func K C (@additive_preadditive C Prod t Add) t (@additive_terminal_object C Prod t
  Add) P (@transf_arrow_diagram_func K C B X b)) (@one_cat_native_snake_kernel_first K C (@additive_preadditive
  C Prod t Add) C1 t (@additive_terminal_object C Prod t Add) T0 P Q A B X D b c h)
  (@one_cat_native_snake_six_term_result K C C1 Prod t Add T0 P Q N A B X D b c h)) (@finite_arrow_tail_arrow
  (Functor_cat K C) (@OneCatNativeExactArrowPair K C (@additive_preadditive C Prod t Add) C1 t
  (@additive_terminal_object C Prod t Add) T0 P Q N) (succ (succ (succ zero))) (@kernel_adjunction_family_func K
  C (@additive_preadditive C Prod t Add) t (@additive_terminal_object C Prod t Add) P
  (@one_cat_native_snake_alpha_diagram K C (@additive_preadditive C Prod t Add) C1 t (@additive_terminal_object
  C Prod t Add) T0 P A B X D b c h)) (@kernel_adjunction_family_func K C (@additive_preadditive C Prod t Add) t
  (@additive_terminal_object C Prod t Add) P (@transf_arrow_diagram_func K C B X b))
  (@one_cat_native_snake_kernel_first K C (@additive_preadditive C Prod t Add) C1 t (@additive_terminal_object C
  Prod t Add) T0 P Q A B X D b c h) (@one_cat_native_snake_six_term_result K C C1 Prod t Add T0 P Q N A B X D b
  c h)) (@finite_arrow_tail_rest (Functor_cat K C) (@OneCatNativeExactArrowPair K C (@additive_preadditive C
  Prod t Add) C1 t (@additive_terminal_object C Prod t Add) T0 P Q N) (succ (succ (succ zero)))
  (@kernel_adjunction_family_func K C (@additive_preadditive C Prod t Add) t (@additive_terminal_object C Prod t
  Add) P (@one_cat_native_snake_alpha_diagram K C (@additive_preadditive C Prod t Add) C1 t
  (@additive_terminal_object C Prod t Add) T0 P A B X D b c h)) (@kernel_adjunction_family_func K C
  (@additive_preadditive C Prod t Add) t (@additive_terminal_object C Prod t Add) P (@transf_arrow_diagram_func
  K C B X b)) (@one_cat_native_snake_kernel_first K C (@additive_preadditive C Prod t Add) C1 t
  (@additive_terminal_object C Prod t Add) T0 P Q A B X D b c h) (@one_cat_native_snake_six_term_result K C C1
  Prod t Add T0 P Q N A B X D b c h))) (@finite_arrow_tail_rest (Functor_cat K C) (@OneCatNativeExactArrowPair K
  C (@additive_preadditive C Prod t Add) C1 t (@additive_terminal_object C Prod t Add) T0 P Q N) (succ (succ
  zero)) (@kernel_adjunction_family_func K C (@additive_preadditive C Prod t Add) t (@additive_terminal_object C
  Prod t Add) P (@transf_arrow_diagram_func K C B X b)) (@finite_arrow_tail_next (Functor_cat K C)
  (@OneCatNativeExactArrowPair K C (@additive_preadditive C Prod t Add) C1 t (@additive_terminal_object C Prod t
  Add) T0 P Q N) (succ (succ (succ zero))) (@kernel_adjunction_family_func K C (@additive_preadditive C Prod t
  Add) t (@additive_terminal_object C Prod t Add) P (@one_cat_native_snake_alpha_diagram K C
  (@additive_preadditive C Prod t Add) C1 t (@additive_terminal_object C Prod t Add) T0 P A B X D b c h))
  (@kernel_adjunction_family_func K C (@additive_preadditive C Prod t Add) t (@additive_terminal_object C Prod t
  Add) P (@transf_arrow_diagram_func K C B X b)) (@one_cat_native_snake_kernel_first K C (@additive_preadditive
  C Prod t Add) C1 t (@additive_terminal_object C Prod t Add) T0 P Q A B X D b c h)
  (@one_cat_native_snake_six_term_result K C C1 Prod t Add T0 P Q N A B X D b c h)) (@finite_arrow_tail_arrow
  (Functor_cat K C) (@OneCatNativeExactArrowPair K C (@additive_preadditive C Prod t Add) C1 t
  (@additive_terminal_object C Prod t Add) T0 P Q N) (succ (succ (succ zero))) (@kernel_adjunction_family_func K
  C (@additive_preadditive C Prod t Add) t (@additive_terminal_object C Prod t Add) P
  (@one_cat_native_snake_alpha_diagram K C (@additive_preadditive C Prod t Add) C1 t (@additive_terminal_object
  C Prod t Add) T0 P A B X D b c h)) (@kernel_adjunction_family_func K C (@additive_preadditive C Prod t Add) t
  (@additive_terminal_object C Prod t Add) P (@transf_arrow_diagram_func K C B X b))
  (@one_cat_native_snake_kernel_first K C (@additive_preadditive C Prod t Add) C1 t (@additive_terminal_object C
  Prod t Add) T0 P Q A B X D b c h) (@one_cat_native_snake_six_term_result K C C1 Prod t Add T0 P Q N A B X D b
  c h)) (@finite_arrow_tail_rest (Functor_cat K C) (@OneCatNativeExactArrowPair K C (@additive_preadditive C
  Prod t Add) C1 t (@additive_terminal_object C Prod t Add) T0 P Q N) (succ (succ (succ zero)))
  (@kernel_adjunction_family_func K C (@additive_preadditive C Prod t Add) t (@additive_terminal_object C Prod t
  Add) P (@one_cat_native_snake_alpha_diagram K C (@additive_preadditive C Prod t Add) C1 t
  (@additive_terminal_object C Prod t Add) T0 P A B X D b c h)) (@kernel_adjunction_family_func K C
  (@additive_preadditive C Prod t Add) t (@additive_terminal_object C Prod t Add) P (@transf_arrow_diagram_func
  K C B X b)) (@one_cat_native_snake_kernel_first K C (@additive_preadditive C Prod t Add) C1 t
  (@additive_terminal_object C Prod t Add) T0 P Q A B X D b c h) (@one_cat_native_snake_six_term_result K C C1
  Prod t Add T0 P Q N A B X D b c h)))) (@finite_arrow_tail_arrow (Functor_cat K C) (@OneCatNativeExactArrowPair
  K C (@additive_preadditive C Prod t Add) C1 t (@additive_terminal_object C Prod t Add) T0 P Q N) (succ zero)
  (@finite_arrow_tail_next (Functor_cat K C) (@OneCatNativeExactArrowPair K C (@additive_preadditive C Prod t
  Add) C1 t (@additive_terminal_object C Prod t Add) T0 P Q N) (succ (succ (succ zero)))
  (@kernel_adjunction_family_func K C (@additive_preadditive C Prod t Add) t (@additive_terminal_object C Prod t
  Add) P (@one_cat_native_snake_alpha_diagram K C (@additive_preadditive C Prod t Add) C1 t
  (@additive_terminal_object C Prod t Add) T0 P A B X D b c h)) (@kernel_adjunction_family_func K C
  (@additive_preadditive C Prod t Add) t (@additive_terminal_object C Prod t Add) P (@transf_arrow_diagram_func
  K C B X b)) (@one_cat_native_snake_kernel_first K C (@additive_preadditive C Prod t Add) C1 t
  (@additive_terminal_object C Prod t Add) T0 P Q A B X D b c h) (@one_cat_native_snake_six_term_result K C C1
  Prod t Add T0 P Q N A B X D b c h)) (@finite_arrow_tail_next (Functor_cat K C) (@OneCatNativeExactArrowPair K
  C (@additive_preadditive C Prod t Add) C1 t (@additive_terminal_object C Prod t Add) T0 P Q N) (succ (succ
  zero)) (@kernel_adjunction_family_func K C (@additive_preadditive C Prod t Add) t (@additive_terminal_object C
  Prod t Add) P (@transf_arrow_diagram_func K C B X b)) (@finite_arrow_tail_next (Functor_cat K C)
  (@OneCatNativeExactArrowPair K C (@additive_preadditive C Prod t Add) C1 t (@additive_terminal_object C Prod t
  Add) T0 P Q N) (succ (succ (succ zero))) (@kernel_adjunction_family_func K C (@additive_preadditive C Prod t
  Add) t (@additive_terminal_object C Prod t Add) P (@one_cat_native_snake_alpha_diagram K C
  (@additive_preadditive C Prod t Add) C1 t (@additive_terminal_object C Prod t Add) T0 P A B X D b c h))
  (@kernel_adjunction_family_func K C (@additive_preadditive C Prod t Add) t (@additive_terminal_object C Prod t
  Add) P (@transf_arrow_diagram_func K C B X b)) (@one_cat_native_snake_kernel_first K C (@additive_preadditive
  C Prod t Add) C1 t (@additive_terminal_object C Prod t Add) T0 P Q A B X D b c h)
  (@one_cat_native_snake_six_term_result K C C1 Prod t Add T0 P Q N A B X D b c h)) (@finite_arrow_tail_arrow
  (Functor_cat K C) (@OneCatNativeExactArrowPair K C (@additive_preadditive C Prod t Add) C1 t
  (@additive_terminal_object C Prod t Add) T0 P Q N) (succ (succ (succ zero))) (@kernel_adjunction_family_func K
  C (@additive_preadditive C Prod t Add) t (@additive_terminal_object C Prod t Add) P
  (@one_cat_native_snake_alpha_diagram K C (@additive_preadditive C Prod t Add) C1 t (@additive_terminal_object
  C Prod t Add) T0 P A B X D b c h)) (@kernel_adjunction_family_func K C (@additive_preadditive C Prod t Add) t
  (@additive_terminal_object C Prod t Add) P (@transf_arrow_diagram_func K C B X b))
  (@one_cat_native_snake_kernel_first K C (@additive_preadditive C Prod t Add) C1 t (@additive_terminal_object C
  Prod t Add) T0 P Q A B X D b c h) (@one_cat_native_snake_six_term_result K C C1 Prod t Add T0 P Q N A B X D b
  c h)) (@finite_arrow_tail_rest (Functor_cat K C) (@OneCatNativeExactArrowPair K C (@additive_preadditive C
  Prod t Add) C1 t (@additive_terminal_object C Prod t Add) T0 P Q N) (succ (succ (succ zero)))
  (@kernel_adjunction_family_func K C (@additive_preadditive C Prod t Add) t (@additive_terminal_object C Prod t
  Add) P (@one_cat_native_snake_alpha_diagram K C (@additive_preadditive C Prod t Add) C1 t
  (@additive_terminal_object C Prod t Add) T0 P A B X D b c h)) (@kernel_adjunction_family_func K C
  (@additive_preadditive C Prod t Add) t (@additive_terminal_object C Prod t Add) P (@transf_arrow_diagram_func
  K C B X b)) (@one_cat_native_snake_kernel_first K C (@additive_preadditive C Prod t Add) C1 t
  (@additive_terminal_object C Prod t Add) T0 P Q A B X D b c h) (@one_cat_native_snake_six_term_result K C C1
  Prod t Add T0 P Q N A B X D b c h))) (@finite_arrow_tail_arrow (Functor_cat K C) (@OneCatNativeExactArrowPair
  K C (@additive_preadditive C Prod t Add) C1 t (@additive_terminal_object C Prod t Add) T0 P Q N) (succ (succ
  zero)) (@kernel_adjunction_family_func K C (@additive_preadditive C Prod t Add) t (@additive_terminal_object C
  Prod t Add) P (@transf_arrow_diagram_func K C B X b)) (@finite_arrow_tail_next (Functor_cat K C)
  (@OneCatNativeExactArrowPair K C (@additive_preadditive C Prod t Add) C1 t (@additive_terminal_object C Prod t
  Add) T0 P Q N) (succ (succ (succ zero))) (@kernel_adjunction_family_func K C (@additive_preadditive C Prod t
  Add) t (@additive_terminal_object C Prod t Add) P (@one_cat_native_snake_alpha_diagram K C
  (@additive_preadditive C Prod t Add) C1 t (@additive_terminal_object C Prod t Add) T0 P A B X D b c h))
  (@kernel_adjunction_family_func K C (@additive_preadditive C Prod t Add) t (@additive_terminal_object C Prod t
  Add) P (@transf_arrow_diagram_func K C B X b)) (@one_cat_native_snake_kernel_first K C (@additive_preadditive
  C Prod t Add) C1 t (@additive_terminal_object C Prod t Add) T0 P Q A B X D b c h)
  (@one_cat_native_snake_six_term_result K C C1 Prod t Add T0 P Q N A B X D b c h)) (@finite_arrow_tail_arrow
  (Functor_cat K C) (@OneCatNativeExactArrowPair K C (@additive_preadditive C Prod t Add) C1 t
  (@additive_terminal_object C Prod t Add) T0 P Q N) (succ (succ (succ zero))) (@kernel_adjunction_family_func K
  C (@additive_preadditive C Prod t Add) t (@additive_terminal_object C Prod t Add) P
  (@one_cat_native_snake_alpha_diagram K C (@additive_preadditive C Prod t Add) C1 t (@additive_terminal_object
  C Prod t Add) T0 P A B X D b c h)) (@kernel_adjunction_family_func K C (@additive_preadditive C Prod t Add) t
  (@additive_terminal_object C Prod t Add) P (@transf_arrow_diagram_func K C B X b))
  (@one_cat_native_snake_kernel_first K C (@additive_preadditive C Prod t Add) C1 t (@additive_terminal_object C
  Prod t Add) T0 P Q A B X D b c h) (@one_cat_native_snake_six_term_result K C C1 Prod t Add T0 P Q N A B X D b
  c h)) (@finite_arrow_tail_rest (Functor_cat K C) (@OneCatNativeExactArrowPair K C (@additive_preadditive C
  Prod t Add) C1 t (@additive_terminal_object C Prod t Add) T0 P Q N) (succ (succ (succ zero)))
  (@kernel_adjunction_family_func K C (@additive_preadditive C Prod t Add) t (@additive_terminal_object C Prod t
  Add) P (@one_cat_native_snake_alpha_diagram K C (@additive_preadditive C Prod t Add) C1 t
  (@additive_terminal_object C Prod t Add) T0 P A B X D b c h)) (@kernel_adjunction_family_func K C
  (@additive_preadditive C Prod t Add) t (@additive_terminal_object C Prod t Add) P (@transf_arrow_diagram_func
  K C B X b)) (@one_cat_native_snake_kernel_first K C (@additive_preadditive C Prod t Add) C1 t
  (@additive_terminal_object C Prod t Add) T0 P Q A B X D b c h) (@one_cat_native_snake_six_term_result K C C1
  Prod t Add T0 P Q N A B X D b c h))) (@finite_arrow_tail_rest (Functor_cat K C) (@OneCatNativeExactArrowPair K
  C (@additive_preadditive C Prod t Add) C1 t (@additive_terminal_object C Prod t Add) T0 P Q N) (succ (succ
  zero)) (@kernel_adjunction_family_func K C (@additive_preadditive C Prod t Add) t (@additive_terminal_object C
  Prod t Add) P (@transf_arrow_diagram_func K C B X b)) (@finite_arrow_tail_next (Functor_cat K C)
  (@OneCatNativeExactArrowPair K C (@additive_preadditive C Prod t Add) C1 t (@additive_terminal_object C Prod t
  Add) T0 P Q N) (succ (succ (succ zero))) (@kernel_adjunction_family_func K C (@additive_preadditive C Prod t
  Add) t (@additive_terminal_object C Prod t Add) P (@one_cat_native_snake_alpha_diagram K C
  (@additive_preadditive C Prod t Add) C1 t (@additive_terminal_object C Prod t Add) T0 P A B X D b c h))
  (@kernel_adjunction_family_func K C (@additive_preadditive C Prod t Add) t (@additive_terminal_object C Prod t
  Add) P (@transf_arrow_diagram_func K C B X b)) (@one_cat_native_snake_kernel_first K C (@additive_preadditive
  C Prod t Add) C1 t (@additive_terminal_object C Prod t Add) T0 P Q A B X D b c h)
  (@one_cat_native_snake_six_term_result K C C1 Prod t Add T0 P Q N A B X D b c h)) (@finite_arrow_tail_arrow
  (Functor_cat K C) (@OneCatNativeExactArrowPair K C (@additive_preadditive C Prod t Add) C1 t
  (@additive_terminal_object C Prod t Add) T0 P Q N) (succ (succ (succ zero))) (@kernel_adjunction_family_func K
  C (@additive_preadditive C Prod t Add) t (@additive_terminal_object C Prod t Add) P
  (@one_cat_native_snake_alpha_diagram K C (@additive_preadditive C Prod t Add) C1 t (@additive_terminal_object
  C Prod t Add) T0 P A B X D b c h)) (@kernel_adjunction_family_func K C (@additive_preadditive C Prod t Add) t
  (@additive_terminal_object C Prod t Add) P (@transf_arrow_diagram_func K C B X b))
  (@one_cat_native_snake_kernel_first K C (@additive_preadditive C Prod t Add) C1 t (@additive_terminal_object C
  Prod t Add) T0 P Q A B X D b c h) (@one_cat_native_snake_six_term_result K C C1 Prod t Add T0 P Q N A B X D b
  c h)) (@finite_arrow_tail_rest (Functor_cat K C) (@OneCatNativeExactArrowPair K C (@additive_preadditive C
  Prod t Add) C1 t (@additive_terminal_object C Prod t Add) T0 P Q N) (succ (succ (succ zero)))
  (@kernel_adjunction_family_func K C (@additive_preadditive C Prod t Add) t (@additive_terminal_object C Prod t
  Add) P (@one_cat_native_snake_alpha_diagram K C (@additive_preadditive C Prod t Add) C1 t
  (@additive_terminal_object C Prod t Add) T0 P A B X D b c h)) (@kernel_adjunction_family_func K C
  (@additive_preadditive C Prod t Add) t (@additive_terminal_object C Prod t Add) P (@transf_arrow_diagram_func
  K C B X b)) (@one_cat_native_snake_kernel_first K C (@additive_preadditive C Prod t Add) C1 t
  (@additive_terminal_object C Prod t Add) T0 P Q A B X D b c h) (@one_cat_native_snake_six_term_result K C C1
  Prod t Add T0 P Q N A B X D b c h)))) (@finite_arrow_tail_rest (Functor_cat K C) (@OneCatNativeExactArrowPair
  K C (@additive_preadditive C Prod t Add) C1 t (@additive_terminal_object C Prod t Add) T0 P Q N) (succ zero)
  (@finite_arrow_tail_next (Functor_cat K C) (@OneCatNativeExactArrowPair K C (@additive_preadditive C Prod t
  Add) C1 t (@additive_terminal_object C Prod t Add) T0 P Q N) (succ (succ (succ zero)))
  (@kernel_adjunction_family_func K C (@additive_preadditive C Prod t Add) t (@additive_terminal_object C Prod t
  Add) P (@one_cat_native_snake_alpha_diagram K C (@additive_preadditive C Prod t Add) C1 t
  (@additive_terminal_object C Prod t Add) T0 P A B X D b c h)) (@kernel_adjunction_family_func K C
  (@additive_preadditive C Prod t Add) t (@additive_terminal_object C Prod t Add) P (@transf_arrow_diagram_func
  K C B X b)) (@one_cat_native_snake_kernel_first K C (@additive_preadditive C Prod t Add) C1 t
  (@additive_terminal_object C Prod t Add) T0 P Q A B X D b c h) (@one_cat_native_snake_six_term_result K C C1
  Prod t Add T0 P Q N A B X D b c h)) (@finite_arrow_tail_next (Functor_cat K C) (@OneCatNativeExactArrowPair K
  C (@additive_preadditive C Prod t Add) C1 t (@additive_terminal_object C Prod t Add) T0 P Q N) (succ (succ
  zero)) (@kernel_adjunction_family_func K C (@additive_preadditive C Prod t Add) t (@additive_terminal_object C
  Prod t Add) P (@transf_arrow_diagram_func K C B X b)) (@finite_arrow_tail_next (Functor_cat K C)
  (@OneCatNativeExactArrowPair K C (@additive_preadditive C Prod t Add) C1 t (@additive_terminal_object C Prod t
  Add) T0 P Q N) (succ (succ (succ zero))) (@kernel_adjunction_family_func K C (@additive_preadditive C Prod t
  Add) t (@additive_terminal_object C Prod t Add) P (@one_cat_native_snake_alpha_diagram K C
  (@additive_preadditive C Prod t Add) C1 t (@additive_terminal_object C Prod t Add) T0 P A B X D b c h))
  (@kernel_adjunction_family_func K C (@additive_preadditive C Prod t Add) t (@additive_terminal_object C Prod t
  Add) P (@transf_arrow_diagram_func K C B X b)) (@one_cat_native_snake_kernel_first K C (@additive_preadditive
  C Prod t Add) C1 t (@additive_terminal_object C Prod t Add) T0 P Q A B X D b c h)
  (@one_cat_native_snake_six_term_result K C C1 Prod t Add T0 P Q N A B X D b c h)) (@finite_arrow_tail_arrow
  (Functor_cat K C) (@OneCatNativeExactArrowPair K C (@additive_preadditive C Prod t Add) C1 t
  (@additive_terminal_object C Prod t Add) T0 P Q N) (succ (succ (succ zero))) (@kernel_adjunction_family_func K
  C (@additive_preadditive C Prod t Add) t (@additive_terminal_object C Prod t Add) P
  (@one_cat_native_snake_alpha_diagram K C (@additive_preadditive C Prod t Add) C1 t (@additive_terminal_object
  C Prod t Add) T0 P A B X D b c h)) (@kernel_adjunction_family_func K C (@additive_preadditive C Prod t Add) t
  (@additive_terminal_object C Prod t Add) P (@transf_arrow_diagram_func K C B X b))
  (@one_cat_native_snake_kernel_first K C (@additive_preadditive C Prod t Add) C1 t (@additive_terminal_object C
  Prod t Add) T0 P Q A B X D b c h) (@one_cat_native_snake_six_term_result K C C1 Prod t Add T0 P Q N A B X D b
  c h)) (@finite_arrow_tail_rest (Functor_cat K C) (@OneCatNativeExactArrowPair K C (@additive_preadditive C
  Prod t Add) C1 t (@additive_terminal_object C Prod t Add) T0 P Q N) (succ (succ (succ zero)))
  (@kernel_adjunction_family_func K C (@additive_preadditive C Prod t Add) t (@additive_terminal_object C Prod t
  Add) P (@one_cat_native_snake_alpha_diagram K C (@additive_preadditive C Prod t Add) C1 t
  (@additive_terminal_object C Prod t Add) T0 P A B X D b c h)) (@kernel_adjunction_family_func K C
  (@additive_preadditive C Prod t Add) t (@additive_terminal_object C Prod t Add) P (@transf_arrow_diagram_func
  K C B X b)) (@one_cat_native_snake_kernel_first K C (@additive_preadditive C Prod t Add) C1 t
  (@additive_terminal_object C Prod t Add) T0 P Q A B X D b c h) (@one_cat_native_snake_six_term_result K C C1
  Prod t Add T0 P Q N A B X D b c h))) (@finite_arrow_tail_arrow (Functor_cat K C) (@OneCatNativeExactArrowPair
  K C (@additive_preadditive C Prod t Add) C1 t (@additive_terminal_object C Prod t Add) T0 P Q N) (succ (succ
  zero)) (@kernel_adjunction_family_func K C (@additive_preadditive C Prod t Add) t (@additive_terminal_object C
  Prod t Add) P (@transf_arrow_diagram_func K C B X b)) (@finite_arrow_tail_next (Functor_cat K C)
  (@OneCatNativeExactArrowPair K C (@additive_preadditive C Prod t Add) C1 t (@additive_terminal_object C Prod t
  Add) T0 P Q N) (succ (succ (succ zero))) (@kernel_adjunction_family_func K C (@additive_preadditive C Prod t
  Add) t (@additive_terminal_object C Prod t Add) P (@one_cat_native_snake_alpha_diagram K C
  (@additive_preadditive C Prod t Add) C1 t (@additive_terminal_object C Prod t Add) T0 P A B X D b c h))
  (@kernel_adjunction_family_func K C (@additive_preadditive C Prod t Add) t (@additive_terminal_object C Prod t
  Add) P (@transf_arrow_diagram_func K C B X b)) (@one_cat_native_snake_kernel_first K C (@additive_preadditive
  C Prod t Add) C1 t (@additive_terminal_object C Prod t Add) T0 P Q A B X D b c h)
  (@one_cat_native_snake_six_term_result K C C1 Prod t Add T0 P Q N A B X D b c h)) (@finite_arrow_tail_arrow
  (Functor_cat K C) (@OneCatNativeExactArrowPair K C (@additive_preadditive C Prod t Add) C1 t
  (@additive_terminal_object C Prod t Add) T0 P Q N) (succ (succ (succ zero))) (@kernel_adjunction_family_func K
  C (@additive_preadditive C Prod t Add) t (@additive_terminal_object C Prod t Add) P
  (@one_cat_native_snake_alpha_diagram K C (@additive_preadditive C Prod t Add) C1 t (@additive_terminal_object
  C Prod t Add) T0 P A B X D b c h)) (@kernel_adjunction_family_func K C (@additive_preadditive C Prod t Add) t
  (@additive_terminal_object C Prod t Add) P (@transf_arrow_diagram_func K C B X b))
  (@one_cat_native_snake_kernel_first K C (@additive_preadditive C Prod t Add) C1 t (@additive_terminal_object C
  Prod t Add) T0 P Q A B X D b c h) (@one_cat_native_snake_six_term_result K C C1 Prod t Add T0 P Q N A B X D b
  c h)) (@finite_arrow_tail_rest (Functor_cat K C) (@OneCatNativeExactArrowPair K C (@additive_preadditive C
  Prod t Add) C1 t (@additive_terminal_object C Prod t Add) T0 P Q N) (succ (succ (succ zero)))
  (@kernel_adjunction_family_func K C (@additive_preadditive C Prod t Add) t (@additive_terminal_object C Prod t
  Add) P (@one_cat_native_snake_alpha_diagram K C (@additive_preadditive C Prod t Add) C1 t
  (@additive_terminal_object C Prod t Add) T0 P A B X D b c h)) (@kernel_adjunction_family_func K C
  (@additive_preadditive C Prod t Add) t (@additive_terminal_object C Prod t Add) P (@transf_arrow_diagram_func
  K C B X b)) (@one_cat_native_snake_kernel_first K C (@additive_preadditive C Prod t Add) C1 t
  (@additive_terminal_object C Prod t Add) T0 P Q A B X D b c h) (@one_cat_native_snake_six_term_result K C C1
  Prod t Add T0 P Q N A B X D b c h))) (@finite_arrow_tail_rest (Functor_cat K C) (@OneCatNativeExactArrowPair K
  C (@additive_preadditive C Prod t Add) C1 t (@additive_terminal_object C Prod t Add) T0 P Q N) (succ (succ
  zero)) (@kernel_adjunction_family_func K C (@additive_preadditive C Prod t Add) t (@additive_terminal_object C
  Prod t Add) P (@transf_arrow_diagram_func K C B X b)) (@finite_arrow_tail_next (Functor_cat K C)
  (@OneCatNativeExactArrowPair K C (@additive_preadditive C Prod t Add) C1 t (@additive_terminal_object C Prod t
  Add) T0 P Q N) (succ (succ (succ zero))) (@kernel_adjunction_family_func K C (@additive_preadditive C Prod t
  Add) t (@additive_terminal_object C Prod t Add) P (@one_cat_native_snake_alpha_diagram K C
  (@additive_preadditive C Prod t Add) C1 t (@additive_terminal_object C Prod t Add) T0 P A B X D b c h))
  (@kernel_adjunction_family_func K C (@additive_preadditive C Prod t Add) t (@additive_terminal_object C Prod t
  Add) P (@transf_arrow_diagram_func K C B X b)) (@one_cat_native_snake_kernel_first K C (@additive_preadditive
  C Prod t Add) C1 t (@additive_terminal_object C Prod t Add) T0 P Q A B X D b c h)
  (@one_cat_native_snake_six_term_result K C C1 Prod t Add T0 P Q N A B X D b c h)) (@finite_arrow_tail_arrow
  (Functor_cat K C) (@OneCatNativeExactArrowPair K C (@additive_preadditive C Prod t Add) C1 t
  (@additive_terminal_object C Prod t Add) T0 P Q N) (succ (succ (succ zero))) (@kernel_adjunction_family_func K
  C (@additive_preadditive C Prod t Add) t (@additive_terminal_object C Prod t Add) P
  (@one_cat_native_snake_alpha_diagram K C (@additive_preadditive C Prod t Add) C1 t (@additive_terminal_object
  C Prod t Add) T0 P A B X D b c h)) (@kernel_adjunction_family_func K C (@additive_preadditive C Prod t Add) t
  (@additive_terminal_object C Prod t Add) P (@transf_arrow_diagram_func K C B X b))
  (@one_cat_native_snake_kernel_first K C (@additive_preadditive C Prod t Add) C1 t (@additive_terminal_object C
  Prod t Add) T0 P Q A B X D b c h) (@one_cat_native_snake_six_term_result K C C1 Prod t Add T0 P Q N A B X D b
  c h)) (@finite_arrow_tail_rest (Functor_cat K C) (@OneCatNativeExactArrowPair K C (@additive_preadditive C
  Prod t Add) C1 t (@additive_terminal_object C Prod t Add) T0 P Q N) (succ (succ (succ zero)))
  (@kernel_adjunction_family_func K C (@additive_preadditive C Prod t Add) t (@additive_terminal_object C Prod t
  Add) P (@one_cat_native_snake_alpha_diagram K C (@additive_preadditive C Prod t Add) C1 t
  (@additive_terminal_object C Prod t Add) T0 P A B X D b c h)) (@kernel_adjunction_family_func K C
  (@additive_preadditive C Prod t Add) t (@additive_terminal_object C Prod t Add) P (@transf_arrow_diagram_func
  K C B X b)) (@one_cat_native_snake_kernel_first K C (@additive_preadditive C Prod t Add) C1 t
  (@additive_terminal_object C Prod t Add) T0 P Q A B X D b c h) (@one_cat_native_snake_six_term_result K C C1
  Prod t Add T0 P Q N A B X D b c h))))) (@finite_arrow_tail_arrow (Functor_cat K C)
  (@OneCatNativeExactArrowPair K C (@additive_preadditive C Prod t Add) C1 t (@additive_terminal_object C Prod t
  Add) T0 P Q N) (succ zero) (@finite_arrow_tail_next (Functor_cat K C) (@OneCatNativeExactArrowPair K C
  (@additive_preadditive C Prod t Add) C1 t (@additive_terminal_object C Prod t Add) T0 P Q N) (succ (succ (succ
  zero))) (@kernel_adjunction_family_func K C (@additive_preadditive C Prod t Add) t (@additive_terminal_object
  C Prod t Add) P (@one_cat_native_snake_alpha_diagram K C (@additive_preadditive C Prod t Add) C1 t
  (@additive_terminal_object C Prod t Add) T0 P A B X D b c h)) (@kernel_adjunction_family_func K C
  (@additive_preadditive C Prod t Add) t (@additive_terminal_object C Prod t Add) P (@transf_arrow_diagram_func
  K C B X b)) (@one_cat_native_snake_kernel_first K C (@additive_preadditive C Prod t Add) C1 t
  (@additive_terminal_object C Prod t Add) T0 P Q A B X D b c h) (@one_cat_native_snake_six_term_result K C C1
  Prod t Add T0 P Q N A B X D b c h)) (@finite_arrow_tail_next (Functor_cat K C) (@OneCatNativeExactArrowPair K
  C (@additive_preadditive C Prod t Add) C1 t (@additive_terminal_object C Prod t Add) T0 P Q N) (succ (succ
  zero)) (@kernel_adjunction_family_func K C (@additive_preadditive C Prod t Add) t (@additive_terminal_object C
  Prod t Add) P (@transf_arrow_diagram_func K C B X b)) (@finite_arrow_tail_next (Functor_cat K C)
  (@OneCatNativeExactArrowPair K C (@additive_preadditive C Prod t Add) C1 t (@additive_terminal_object C Prod t
  Add) T0 P Q N) (succ (succ (succ zero))) (@kernel_adjunction_family_func K C (@additive_preadditive C Prod t
  Add) t (@additive_terminal_object C Prod t Add) P (@one_cat_native_snake_alpha_diagram K C
  (@additive_preadditive C Prod t Add) C1 t (@additive_terminal_object C Prod t Add) T0 P A B X D b c h))
  (@kernel_adjunction_family_func K C (@additive_preadditive C Prod t Add) t (@additive_terminal_object C Prod t
  Add) P (@transf_arrow_diagram_func K C B X b)) (@one_cat_native_snake_kernel_first K C (@additive_preadditive
  C Prod t Add) C1 t (@additive_terminal_object C Prod t Add) T0 P Q A B X D b c h)
  (@one_cat_native_snake_six_term_result K C C1 Prod t Add T0 P Q N A B X D b c h)) (@finite_arrow_tail_arrow
  (Functor_cat K C) (@OneCatNativeExactArrowPair K C (@additive_preadditive C Prod t Add) C1 t
  (@additive_terminal_object C Prod t Add) T0 P Q N) (succ (succ (succ zero))) (@kernel_adjunction_family_func K
  C (@additive_preadditive C Prod t Add) t (@additive_terminal_object C Prod t Add) P
  (@one_cat_native_snake_alpha_diagram K C (@additive_preadditive C Prod t Add) C1 t (@additive_terminal_object
  C Prod t Add) T0 P A B X D b c h)) (@kernel_adjunction_family_func K C (@additive_preadditive C Prod t Add) t
  (@additive_terminal_object C Prod t Add) P (@transf_arrow_diagram_func K C B X b))
  (@one_cat_native_snake_kernel_first K C (@additive_preadditive C Prod t Add) C1 t (@additive_terminal_object C
  Prod t Add) T0 P Q A B X D b c h) (@one_cat_native_snake_six_term_result K C C1 Prod t Add T0 P Q N A B X D b
  c h)) (@finite_arrow_tail_rest (Functor_cat K C) (@OneCatNativeExactArrowPair K C (@additive_preadditive C
  Prod t Add) C1 t (@additive_terminal_object C Prod t Add) T0 P Q N) (succ (succ (succ zero)))
  (@kernel_adjunction_family_func K C (@additive_preadditive C Prod t Add) t (@additive_terminal_object C Prod t
  Add) P (@one_cat_native_snake_alpha_diagram K C (@additive_preadditive C Prod t Add) C1 t
  (@additive_terminal_object C Prod t Add) T0 P A B X D b c h)) (@kernel_adjunction_family_func K C
  (@additive_preadditive C Prod t Add) t (@additive_terminal_object C Prod t Add) P (@transf_arrow_diagram_func
  K C B X b)) (@one_cat_native_snake_kernel_first K C (@additive_preadditive C Prod t Add) C1 t
  (@additive_terminal_object C Prod t Add) T0 P Q A B X D b c h) (@one_cat_native_snake_six_term_result K C C1
  Prod t Add T0 P Q N A B X D b c h))) (@finite_arrow_tail_arrow (Functor_cat K C) (@OneCatNativeExactArrowPair
  K C (@additive_preadditive C Prod t Add) C1 t (@additive_terminal_object C Prod t Add) T0 P Q N) (succ (succ
  zero)) (@kernel_adjunction_family_func K C (@additive_preadditive C Prod t Add) t (@additive_terminal_object C
  Prod t Add) P (@transf_arrow_diagram_func K C B X b)) (@finite_arrow_tail_next (Functor_cat K C)
  (@OneCatNativeExactArrowPair K C (@additive_preadditive C Prod t Add) C1 t (@additive_terminal_object C Prod t
  Add) T0 P Q N) (succ (succ (succ zero))) (@kernel_adjunction_family_func K C (@additive_preadditive C Prod t
  Add) t (@additive_terminal_object C Prod t Add) P (@one_cat_native_snake_alpha_diagram K C
  (@additive_preadditive C Prod t Add) C1 t (@additive_terminal_object C Prod t Add) T0 P A B X D b c h))
  (@kernel_adjunction_family_func K C (@additive_preadditive C Prod t Add) t (@additive_terminal_object C Prod t
  Add) P (@transf_arrow_diagram_func K C B X b)) (@one_cat_native_snake_kernel_first K C (@additive_preadditive
  C Prod t Add) C1 t (@additive_terminal_object C Prod t Add) T0 P Q A B X D b c h)
  (@one_cat_native_snake_six_term_result K C C1 Prod t Add T0 P Q N A B X D b c h)) (@finite_arrow_tail_arrow
  (Functor_cat K C) (@OneCatNativeExactArrowPair K C (@additive_preadditive C Prod t Add) C1 t
  (@additive_terminal_object C Prod t Add) T0 P Q N) (succ (succ (succ zero))) (@kernel_adjunction_family_func K
  C (@additive_preadditive C Prod t Add) t (@additive_terminal_object C Prod t Add) P
  (@one_cat_native_snake_alpha_diagram K C (@additive_preadditive C Prod t Add) C1 t (@additive_terminal_object
  C Prod t Add) T0 P A B X D b c h)) (@kernel_adjunction_family_func K C (@additive_preadditive C Prod t Add) t
  (@additive_terminal_object C Prod t Add) P (@transf_arrow_diagram_func K C B X b))
  (@one_cat_native_snake_kernel_first K C (@additive_preadditive C Prod t Add) C1 t (@additive_terminal_object C
  Prod t Add) T0 P Q A B X D b c h) (@one_cat_native_snake_six_term_result K C C1 Prod t Add T0 P Q N A B X D b
  c h)) (@finite_arrow_tail_rest (Functor_cat K C) (@OneCatNativeExactArrowPair K C (@additive_preadditive C
  Prod t Add) C1 t (@additive_terminal_object C Prod t Add) T0 P Q N) (succ (succ (succ zero)))
  (@kernel_adjunction_family_func K C (@additive_preadditive C Prod t Add) t (@additive_terminal_object C Prod t
  Add) P (@one_cat_native_snake_alpha_diagram K C (@additive_preadditive C Prod t Add) C1 t
  (@additive_terminal_object C Prod t Add) T0 P A B X D b c h)) (@kernel_adjunction_family_func K C
  (@additive_preadditive C Prod t Add) t (@additive_terminal_object C Prod t Add) P (@transf_arrow_diagram_func
  K C B X b)) (@one_cat_native_snake_kernel_first K C (@additive_preadditive C Prod t Add) C1 t
  (@additive_terminal_object C Prod t Add) T0 P Q A B X D b c h) (@one_cat_native_snake_six_term_result K C C1
  Prod t Add T0 P Q N A B X D b c h))) (@finite_arrow_tail_rest (Functor_cat K C) (@OneCatNativeExactArrowPair K
  C (@additive_preadditive C Prod t Add) C1 t (@additive_terminal_object C Prod t Add) T0 P Q N) (succ (succ
  zero)) (@kernel_adjunction_family_func K C (@additive_preadditive C Prod t Add) t (@additive_terminal_object C
  Prod t Add) P (@transf_arrow_diagram_func K C B X b)) (@finite_arrow_tail_next (Functor_cat K C)
  (@OneCatNativeExactArrowPair K C (@additive_preadditive C Prod t Add) C1 t (@additive_terminal_object C Prod t
  Add) T0 P Q N) (succ (succ (succ zero))) (@kernel_adjunction_family_func K C (@additive_preadditive C Prod t
  Add) t (@additive_terminal_object C Prod t Add) P (@one_cat_native_snake_alpha_diagram K C
  (@additive_preadditive C Prod t Add) C1 t (@additive_terminal_object C Prod t Add) T0 P A B X D b c h))
  (@kernel_adjunction_family_func K C (@additive_preadditive C Prod t Add) t (@additive_terminal_object C Prod t
  Add) P (@transf_arrow_diagram_func K C B X b)) (@one_cat_native_snake_kernel_first K C (@additive_preadditive
  C Prod t Add) C1 t (@additive_terminal_object C Prod t Add) T0 P Q A B X D b c h)
  (@one_cat_native_snake_six_term_result K C C1 Prod t Add T0 P Q N A B X D b c h)) (@finite_arrow_tail_arrow
  (Functor_cat K C) (@OneCatNativeExactArrowPair K C (@additive_preadditive C Prod t Add) C1 t
  (@additive_terminal_object C Prod t Add) T0 P Q N) (succ (succ (succ zero))) (@kernel_adjunction_family_func K
  C (@additive_preadditive C Prod t Add) t (@additive_terminal_object C Prod t Add) P
  (@one_cat_native_snake_alpha_diagram K C (@additive_preadditive C Prod t Add) C1 t (@additive_terminal_object
  C Prod t Add) T0 P A B X D b c h)) (@kernel_adjunction_family_func K C (@additive_preadditive C Prod t Add) t
  (@additive_terminal_object C Prod t Add) P (@transf_arrow_diagram_func K C B X b))
  (@one_cat_native_snake_kernel_first K C (@additive_preadditive C Prod t Add) C1 t (@additive_terminal_object C
  Prod t Add) T0 P Q A B X D b c h) (@one_cat_native_snake_six_term_result K C C1 Prod t Add T0 P Q N A B X D b
  c h)) (@finite_arrow_tail_rest (Functor_cat K C) (@OneCatNativeExactArrowPair K C (@additive_preadditive C
  Prod t Add) C1 t (@additive_terminal_object C Prod t Add) T0 P Q N) (succ (succ (succ zero)))
  (@kernel_adjunction_family_func K C (@additive_preadditive C Prod t Add) t (@additive_terminal_object C Prod t
  Add) P (@one_cat_native_snake_alpha_diagram K C (@additive_preadditive C Prod t Add) C1 t
  (@additive_terminal_object C Prod t Add) T0 P A B X D b c h)) (@kernel_adjunction_family_func K C
  (@additive_preadditive C Prod t Add) t (@additive_terminal_object C Prod t Add) P (@transf_arrow_diagram_func
  K C B X b)) (@one_cat_native_snake_kernel_first K C (@additive_preadditive C Prod t Add) C1 t
  (@additive_terminal_object C Prod t Add) T0 P Q A B X D b c h) (@one_cat_native_snake_six_term_result K C C1
  Prod t Add T0 P Q N A B X D b c h)))) (@finite_arrow_tail_arrow (Functor_cat K C) (@OneCatNativeExactArrowPair
  K C (@additive_preadditive C Prod t Add) C1 t (@additive_terminal_object C Prod t Add) T0 P Q N) zero
  (@finite_arrow_tail_next (Functor_cat K C) (@OneCatNativeExactArrowPair K C (@additive_preadditive C Prod t
  Add) C1 t (@additive_terminal_object C Prod t Add) T0 P Q N) (succ (succ zero))
  (@kernel_adjunction_family_func K C (@additive_preadditive C Prod t Add) t (@additive_terminal_object C Prod t
  Add) P (@transf_arrow_diagram_func K C B X b)) (@finite_arrow_tail_next (Functor_cat K C)
  (@OneCatNativeExactArrowPair K C (@additive_preadditive C Prod t Add) C1 t (@additive_terminal_object C Prod t
  Add) T0 P Q N) (succ (succ (succ zero))) (@kernel_adjunction_family_func K C (@additive_preadditive C Prod t
  Add) t (@additive_terminal_object C Prod t Add) P (@one_cat_native_snake_alpha_diagram K C
  (@additive_preadditive C Prod t Add) C1 t (@additive_terminal_object C Prod t Add) T0 P A B X D b c h))
  (@kernel_adjunction_family_func K C (@additive_preadditive C Prod t Add) t (@additive_terminal_object C Prod t
  Add) P (@transf_arrow_diagram_func K C B X b)) (@one_cat_native_snake_kernel_first K C (@additive_preadditive
  C Prod t Add) C1 t (@additive_terminal_object C Prod t Add) T0 P Q A B X D b c h)
  (@one_cat_native_snake_six_term_result K C C1 Prod t Add T0 P Q N A B X D b c h)) (@finite_arrow_tail_arrow
  (Functor_cat K C) (@OneCatNativeExactArrowPair K C (@additive_preadditive C Prod t Add) C1 t
  (@additive_terminal_object C Prod t Add) T0 P Q N) (succ (succ (succ zero))) (@kernel_adjunction_family_func K
  C (@additive_preadditive C Prod t Add) t (@additive_terminal_object C Prod t Add) P
  (@one_cat_native_snake_alpha_diagram K C (@additive_preadditive C Prod t Add) C1 t (@additive_terminal_object
  C Prod t Add) T0 P A B X D b c h)) (@kernel_adjunction_family_func K C (@additive_preadditive C Prod t Add) t
  (@additive_terminal_object C Prod t Add) P (@transf_arrow_diagram_func K C B X b))
  (@one_cat_native_snake_kernel_first K C (@additive_preadditive C Prod t Add) C1 t (@additive_terminal_object C
  Prod t Add) T0 P Q A B X D b c h) (@one_cat_native_snake_six_term_result K C C1 Prod t Add T0 P Q N A B X D b
  c h)) (@finite_arrow_tail_rest (Functor_cat K C) (@OneCatNativeExactArrowPair K C (@additive_preadditive C
  Prod t Add) C1 t (@additive_terminal_object C Prod t Add) T0 P Q N) (succ (succ (succ zero)))
  (@kernel_adjunction_family_func K C (@additive_preadditive C Prod t Add) t (@additive_terminal_object C Prod t
  Add) P (@one_cat_native_snake_alpha_diagram K C (@additive_preadditive C Prod t Add) C1 t
  (@additive_terminal_object C Prod t Add) T0 P A B X D b c h)) (@kernel_adjunction_family_func K C
  (@additive_preadditive C Prod t Add) t (@additive_terminal_object C Prod t Add) P (@transf_arrow_diagram_func
  K C B X b)) (@one_cat_native_snake_kernel_first K C (@additive_preadditive C Prod t Add) C1 t
  (@additive_terminal_object C Prod t Add) T0 P Q A B X D b c h) (@one_cat_native_snake_six_term_result K C C1
  Prod t Add T0 P Q N A B X D b c h))) (@finite_arrow_tail_next (Functor_cat K C) (@OneCatNativeExactArrowPair K
  C (@additive_preadditive C Prod t Add) C1 t (@additive_terminal_object C Prod t Add) T0 P Q N) (succ zero)
  (@finite_arrow_tail_next (Functor_cat K C) (@OneCatNativeExactArrowPair K C (@additive_preadditive C Prod t
  Add) C1 t (@additive_terminal_object C Prod t Add) T0 P Q N) (succ (succ (succ zero)))
  (@kernel_adjunction_family_func K C (@additive_preadditive C Prod t Add) t (@additive_terminal_object C Prod t
  Add) P (@one_cat_native_snake_alpha_diagram K C (@additive_preadditive C Prod t Add) C1 t
  (@additive_terminal_object C Prod t Add) T0 P A B X D b c h)) (@kernel_adjunction_family_func K C
  (@additive_preadditive C Prod t Add) t (@additive_terminal_object C Prod t Add) P (@transf_arrow_diagram_func
  K C B X b)) (@one_cat_native_snake_kernel_first K C (@additive_preadditive C Prod t Add) C1 t
  (@additive_terminal_object C Prod t Add) T0 P Q A B X D b c h) (@one_cat_native_snake_six_term_result K C C1
  Prod t Add T0 P Q N A B X D b c h)) (@finite_arrow_tail_next (Functor_cat K C) (@OneCatNativeExactArrowPair K
  C (@additive_preadditive C Prod t Add) C1 t (@additive_terminal_object C Prod t Add) T0 P Q N) (succ (succ
  zero)) (@kernel_adjunction_family_func K C (@additive_preadditive C Prod t Add) t (@additive_terminal_object C
  Prod t Add) P (@transf_arrow_diagram_func K C B X b)) (@finite_arrow_tail_next (Functor_cat K C)
  (@OneCatNativeExactArrowPair K C (@additive_preadditive C Prod t Add) C1 t (@additive_terminal_object C Prod t
  Add) T0 P Q N) (succ (succ (succ zero))) (@kernel_adjunction_family_func K C (@additive_preadditive C Prod t
  Add) t (@additive_terminal_object C Prod t Add) P (@one_cat_native_snake_alpha_diagram K C
  (@additive_preadditive C Prod t Add) C1 t (@additive_terminal_object C Prod t Add) T0 P A B X D b c h))
  (@kernel_adjunction_family_func K C (@additive_preadditive C Prod t Add) t (@additive_terminal_object C Prod t
  Add) P (@transf_arrow_diagram_func K C B X b)) (@one_cat_native_snake_kernel_first K C (@additive_preadditive
  C Prod t Add) C1 t (@additive_terminal_object C Prod t Add) T0 P Q A B X D b c h)
  (@one_cat_native_snake_six_term_result K C C1 Prod t Add T0 P Q N A B X D b c h)) (@finite_arrow_tail_arrow
  (Functor_cat K C) (@OneCatNativeExactArrowPair K C (@additive_preadditive C Prod t Add) C1 t
  (@additive_terminal_object C Prod t Add) T0 P Q N) (succ (succ (succ zero))) (@kernel_adjunction_family_func K
  C (@additive_preadditive C Prod t Add) t (@additive_terminal_object C Prod t Add) P
  (@one_cat_native_snake_alpha_diagram K C (@additive_preadditive C Prod t Add) C1 t (@additive_terminal_object
  C Prod t Add) T0 P A B X D b c h)) (@kernel_adjunction_family_func K C (@additive_preadditive C Prod t Add) t
  (@additive_terminal_object C Prod t Add) P (@transf_arrow_diagram_func K C B X b))
  (@one_cat_native_snake_kernel_first K C (@additive_preadditive C Prod t Add) C1 t (@additive_terminal_object C
  Prod t Add) T0 P Q A B X D b c h) (@one_cat_native_snake_six_term_result K C C1 Prod t Add T0 P Q N A B X D b
  c h)) (@finite_arrow_tail_rest (Functor_cat K C) (@OneCatNativeExactArrowPair K C (@additive_preadditive C
  Prod t Add) C1 t (@additive_terminal_object C Prod t Add) T0 P Q N) (succ (succ (succ zero)))
  (@kernel_adjunction_family_func K C (@additive_preadditive C Prod t Add) t (@additive_terminal_object C Prod t
  Add) P (@one_cat_native_snake_alpha_diagram K C (@additive_preadditive C Prod t Add) C1 t
  (@additive_terminal_object C Prod t Add) T0 P A B X D b c h)) (@kernel_adjunction_family_func K C
  (@additive_preadditive C Prod t Add) t (@additive_terminal_object C Prod t Add) P (@transf_arrow_diagram_func
  K C B X b)) (@one_cat_native_snake_kernel_first K C (@additive_preadditive C Prod t Add) C1 t
  (@additive_terminal_object C Prod t Add) T0 P Q A B X D b c h) (@one_cat_native_snake_six_term_result K C C1
  Prod t Add T0 P Q N A B X D b c h))) (@finite_arrow_tail_arrow (Functor_cat K C) (@OneCatNativeExactArrowPair
  K C (@additive_preadditive C Prod t Add) C1 t (@additive_terminal_object C Prod t Add) T0 P Q N) (succ (succ
  zero)) (@kernel_adjunction_family_func K C (@additive_preadditive C Prod t Add) t (@additive_terminal_object C
  Prod t Add) P (@transf_arrow_diagram_func K C B X b)) (@finite_arrow_tail_next (Functor_cat K C)
  (@OneCatNativeExactArrowPair K C (@additive_preadditive C Prod t Add) C1 t (@additive_terminal_object C Prod t
  Add) T0 P Q N) (succ (succ (succ zero))) (@kernel_adjunction_family_func K C (@additive_preadditive C Prod t
  Add) t (@additive_terminal_object C Prod t Add) P (@one_cat_native_snake_alpha_diagram K C
  (@additive_preadditive C Prod t Add) C1 t (@additive_terminal_object C Prod t Add) T0 P A B X D b c h))
  (@kernel_adjunction_family_func K C (@additive_preadditive C Prod t Add) t (@additive_terminal_object C Prod t
  Add) P (@transf_arrow_diagram_func K C B X b)) (@one_cat_native_snake_kernel_first K C (@additive_preadditive
  C Prod t Add) C1 t (@additive_terminal_object C Prod t Add) T0 P Q A B X D b c h)
  (@one_cat_native_snake_six_term_result K C C1 Prod t Add T0 P Q N A B X D b c h)) (@finite_arrow_tail_arrow
  (Functor_cat K C) (@OneCatNativeExactArrowPair K C (@additive_preadditive C Prod t Add) C1 t
  (@additive_terminal_object C Prod t Add) T0 P Q N) (succ (succ (succ zero))) (@kernel_adjunction_family_func K
  C (@additive_preadditive C Prod t Add) t (@additive_terminal_object C Prod t Add) P
  (@one_cat_native_snake_alpha_diagram K C (@additive_preadditive C Prod t Add) C1 t (@additive_terminal_object
  C Prod t Add) T0 P A B X D b c h)) (@kernel_adjunction_family_func K C (@additive_preadditive C Prod t Add) t
  (@additive_terminal_object C Prod t Add) P (@transf_arrow_diagram_func K C B X b))
  (@one_cat_native_snake_kernel_first K C (@additive_preadditive C Prod t Add) C1 t (@additive_terminal_object C
  Prod t Add) T0 P Q A B X D b c h) (@one_cat_native_snake_six_term_result K C C1 Prod t Add T0 P Q N A B X D b
  c h)) (@finite_arrow_tail_rest (Functor_cat K C) (@OneCatNativeExactArrowPair K C (@additive_preadditive C
  Prod t Add) C1 t (@additive_terminal_object C Prod t Add) T0 P Q N) (succ (succ (succ zero)))
  (@kernel_adjunction_family_func K C (@additive_preadditive C Prod t Add) t (@additive_terminal_object C Prod t
  Add) P (@one_cat_native_snake_alpha_diagram K C (@additive_preadditive C Prod t Add) C1 t
  (@additive_terminal_object C Prod t Add) T0 P A B X D b c h)) (@kernel_adjunction_family_func K C
  (@additive_preadditive C Prod t Add) t (@additive_terminal_object C Prod t Add) P (@transf_arrow_diagram_func
  K C B X b)) (@one_cat_native_snake_kernel_first K C (@additive_preadditive C Prod t Add) C1 t
  (@additive_terminal_object C Prod t Add) T0 P Q A B X D b c h) (@one_cat_native_snake_six_term_result K C C1
  Prod t Add T0 P Q N A B X D b c h))) (@finite_arrow_tail_rest (Functor_cat K C) (@OneCatNativeExactArrowPair K
  C (@additive_preadditive C Prod t Add) C1 t (@additive_terminal_object C Prod t Add) T0 P Q N) (succ (succ
  zero)) (@kernel_adjunction_family_func K C (@additive_preadditive C Prod t Add) t (@additive_terminal_object C
  Prod t Add) P (@transf_arrow_diagram_func K C B X b)) (@finite_arrow_tail_next (Functor_cat K C)
  (@OneCatNativeExactArrowPair K C (@additive_preadditive C Prod t Add) C1 t (@additive_terminal_object C Prod t
  Add) T0 P Q N) (succ (succ (succ zero))) (@kernel_adjunction_family_func K C (@additive_preadditive C Prod t
  Add) t (@additive_terminal_object C Prod t Add) P (@one_cat_native_snake_alpha_diagram K C
  (@additive_preadditive C Prod t Add) C1 t (@additive_terminal_object C Prod t Add) T0 P A B X D b c h))
  (@kernel_adjunction_family_func K C (@additive_preadditive C Prod t Add) t (@additive_terminal_object C Prod t
  Add) P (@transf_arrow_diagram_func K C B X b)) (@one_cat_native_snake_kernel_first K C (@additive_preadditive
  C Prod t Add) C1 t (@additive_terminal_object C Prod t Add) T0 P Q A B X D b c h)
  (@one_cat_native_snake_six_term_result K C C1 Prod t Add T0 P Q N A B X D b c h)) (@finite_arrow_tail_arrow
  (Functor_cat K C) (@OneCatNativeExactArrowPair K C (@additive_preadditive C Prod t Add) C1 t
  (@additive_terminal_object C Prod t Add) T0 P Q N) (succ (succ (succ zero))) (@kernel_adjunction_family_func K
  C (@additive_preadditive C Prod t Add) t (@additive_terminal_object C Prod t Add) P
  (@one_cat_native_snake_alpha_diagram K C (@additive_preadditive C Prod t Add) C1 t (@additive_terminal_object
  C Prod t Add) T0 P A B X D b c h)) (@kernel_adjunction_family_func K C (@additive_preadditive C Prod t Add) t
  (@additive_terminal_object C Prod t Add) P (@transf_arrow_diagram_func K C B X b))
  (@one_cat_native_snake_kernel_first K C (@additive_preadditive C Prod t Add) C1 t (@additive_terminal_object C
  Prod t Add) T0 P Q A B X D b c h) (@one_cat_native_snake_six_term_result K C C1 Prod t Add T0 P Q N A B X D b
  c h)) (@finite_arrow_tail_rest (Functor_cat K C) (@OneCatNativeExactArrowPair K C (@additive_preadditive C
  Prod t Add) C1 t (@additive_terminal_object C Prod t Add) T0 P Q N) (succ (succ (succ zero)))
  (@kernel_adjunction_family_func K C (@additive_preadditive C Prod t Add) t (@additive_terminal_object C Prod t
  Add) P (@one_cat_native_snake_alpha_diagram K C (@additive_preadditive C Prod t Add) C1 t
  (@additive_terminal_object C Prod t Add) T0 P A B X D b c h)) (@kernel_adjunction_family_func K C
  (@additive_preadditive C Prod t Add) t (@additive_terminal_object C Prod t Add) P (@transf_arrow_diagram_func
  K C B X b)) (@one_cat_native_snake_kernel_first K C (@additive_preadditive C Prod t Add) C1 t
  (@additive_terminal_object C Prod t Add) T0 P Q A B X D b c h) (@one_cat_native_snake_six_term_result K C C1
  Prod t Add T0 P Q N A B X D b c h)))) (@finite_arrow_tail_arrow (Functor_cat K C) (@OneCatNativeExactArrowPair
  K C (@additive_preadditive C Prod t Add) C1 t (@additive_terminal_object C Prod t Add) T0 P Q N) (succ zero)
  (@finite_arrow_tail_next (Functor_cat K C) (@OneCatNativeExactArrowPair K C (@additive_preadditive C Prod t
  Add) C1 t (@additive_terminal_object C Prod t Add) T0 P Q N) (succ (succ (succ zero)))
  (@kernel_adjunction_family_func K C (@additive_preadditive C Prod t Add) t (@additive_terminal_object C Prod t
  Add) P (@one_cat_native_snake_alpha_diagram K C (@additive_preadditive C Prod t Add) C1 t
  (@additive_terminal_object C Prod t Add) T0 P A B X D b c h)) (@kernel_adjunction_family_func K C
  (@additive_preadditive C Prod t Add) t (@additive_terminal_object C Prod t Add) P (@transf_arrow_diagram_func
  K C B X b)) (@one_cat_native_snake_kernel_first K C (@additive_preadditive C Prod t Add) C1 t
  (@additive_terminal_object C Prod t Add) T0 P Q A B X D b c h) (@one_cat_native_snake_six_term_result K C C1
  Prod t Add T0 P Q N A B X D b c h)) (@finite_arrow_tail_next (Functor_cat K C) (@OneCatNativeExactArrowPair K
  C (@additive_preadditive C Prod t Add) C1 t (@additive_terminal_object C Prod t Add) T0 P Q N) (succ (succ
  zero)) (@kernel_adjunction_family_func K C (@additive_preadditive C Prod t Add) t (@additive_terminal_object C
  Prod t Add) P (@transf_arrow_diagram_func K C B X b)) (@finite_arrow_tail_next (Functor_cat K C)
  (@OneCatNativeExactArrowPair K C (@additive_preadditive C Prod t Add) C1 t (@additive_terminal_object C Prod t
  Add) T0 P Q N) (succ (succ (succ zero))) (@kernel_adjunction_family_func K C (@additive_preadditive C Prod t
  Add) t (@additive_terminal_object C Prod t Add) P (@one_cat_native_snake_alpha_diagram K C
  (@additive_preadditive C Prod t Add) C1 t (@additive_terminal_object C Prod t Add) T0 P A B X D b c h))
  (@kernel_adjunction_family_func K C (@additive_preadditive C Prod t Add) t (@additive_terminal_object C Prod t
  Add) P (@transf_arrow_diagram_func K C B X b)) (@one_cat_native_snake_kernel_first K C (@additive_preadditive
  C Prod t Add) C1 t (@additive_terminal_object C Prod t Add) T0 P Q A B X D b c h)
  (@one_cat_native_snake_six_term_result K C C1 Prod t Add T0 P Q N A B X D b c h)) (@finite_arrow_tail_arrow
  (Functor_cat K C) (@OneCatNativeExactArrowPair K C (@additive_preadditive C Prod t Add) C1 t
  (@additive_terminal_object C Prod t Add) T0 P Q N) (succ (succ (succ zero))) (@kernel_adjunction_family_func K
  C (@additive_preadditive C Prod t Add) t (@additive_terminal_object C Prod t Add) P
  (@one_cat_native_snake_alpha_diagram K C (@additive_preadditive C Prod t Add) C1 t (@additive_terminal_object
  C Prod t Add) T0 P A B X D b c h)) (@kernel_adjunction_family_func K C (@additive_preadditive C Prod t Add) t
  (@additive_terminal_object C Prod t Add) P (@transf_arrow_diagram_func K C B X b))
  (@one_cat_native_snake_kernel_first K C (@additive_preadditive C Prod t Add) C1 t (@additive_terminal_object C
  Prod t Add) T0 P Q A B X D b c h) (@one_cat_native_snake_six_term_result K C C1 Prod t Add T0 P Q N A B X D b
  c h)) (@finite_arrow_tail_rest (Functor_cat K C) (@OneCatNativeExactArrowPair K C (@additive_preadditive C
  Prod t Add) C1 t (@additive_terminal_object C Prod t Add) T0 P Q N) (succ (succ (succ zero)))
  (@kernel_adjunction_family_func K C (@additive_preadditive C Prod t Add) t (@additive_terminal_object C Prod t
  Add) P (@one_cat_native_snake_alpha_diagram K C (@additive_preadditive C Prod t Add) C1 t
  (@additive_terminal_object C Prod t Add) T0 P A B X D b c h)) (@kernel_adjunction_family_func K C
  (@additive_preadditive C Prod t Add) t (@additive_terminal_object C Prod t Add) P (@transf_arrow_diagram_func
  K C B X b)) (@one_cat_native_snake_kernel_first K C (@additive_preadditive C Prod t Add) C1 t
  (@additive_terminal_object C Prod t Add) T0 P Q A B X D b c h) (@one_cat_native_snake_six_term_result K C C1
  Prod t Add T0 P Q N A B X D b c h))) (@finite_arrow_tail_arrow (Functor_cat K C) (@OneCatNativeExactArrowPair
  K C (@additive_preadditive C Prod t Add) C1 t (@additive_terminal_object C Prod t Add) T0 P Q N) (succ (succ
  zero)) (@kernel_adjunction_family_func K C (@additive_preadditive C Prod t Add) t (@additive_terminal_object C
  Prod t Add) P (@transf_arrow_diagram_func K C B X b)) (@finite_arrow_tail_next (Functor_cat K C)
  (@OneCatNativeExactArrowPair K C (@additive_preadditive C Prod t Add) C1 t (@additive_terminal_object C Prod t
  Add) T0 P Q N) (succ (succ (succ zero))) (@kernel_adjunction_family_func K C (@additive_preadditive C Prod t
  Add) t (@additive_terminal_object C Prod t Add) P (@one_cat_native_snake_alpha_diagram K C
  (@additive_preadditive C Prod t Add) C1 t (@additive_terminal_object C Prod t Add) T0 P A B X D b c h))
  (@kernel_adjunction_family_func K C (@additive_preadditive C Prod t Add) t (@additive_terminal_object C Prod t
  Add) P (@transf_arrow_diagram_func K C B X b)) (@one_cat_native_snake_kernel_first K C (@additive_preadditive
  C Prod t Add) C1 t (@additive_terminal_object C Prod t Add) T0 P Q A B X D b c h)
  (@one_cat_native_snake_six_term_result K C C1 Prod t Add T0 P Q N A B X D b c h)) (@finite_arrow_tail_arrow
  (Functor_cat K C) (@OneCatNativeExactArrowPair K C (@additive_preadditive C Prod t Add) C1 t
  (@additive_terminal_object C Prod t Add) T0 P Q N) (succ (succ (succ zero))) (@kernel_adjunction_family_func K
  C (@additive_preadditive C Prod t Add) t (@additive_terminal_object C Prod t Add) P
  (@one_cat_native_snake_alpha_diagram K C (@additive_preadditive C Prod t Add) C1 t (@additive_terminal_object
  C Prod t Add) T0 P A B X D b c h)) (@kernel_adjunction_family_func K C (@additive_preadditive C Prod t Add) t
  (@additive_terminal_object C Prod t Add) P (@transf_arrow_diagram_func K C B X b))
  (@one_cat_native_snake_kernel_first K C (@additive_preadditive C Prod t Add) C1 t (@additive_terminal_object C
  Prod t Add) T0 P Q A B X D b c h) (@one_cat_native_snake_six_term_result K C C1 Prod t Add T0 P Q N A B X D b
  c h)) (@finite_arrow_tail_rest (Functor_cat K C) (@OneCatNativeExactArrowPair K C (@additive_preadditive C
  Prod t Add) C1 t (@additive_terminal_object C Prod t Add) T0 P Q N) (succ (succ (succ zero)))
  (@kernel_adjunction_family_func K C (@additive_preadditive C Prod t Add) t (@additive_terminal_object C Prod t
  Add) P (@one_cat_native_snake_alpha_diagram K C (@additive_preadditive C Prod t Add) C1 t
  (@additive_terminal_object C Prod t Add) T0 P A B X D b c h)) (@kernel_adjunction_family_func K C
  (@additive_preadditive C Prod t Add) t (@additive_terminal_object C Prod t Add) P (@transf_arrow_diagram_func
  K C B X b)) (@one_cat_native_snake_kernel_first K C (@additive_preadditive C Prod t Add) C1 t
  (@additive_terminal_object C Prod t Add) T0 P Q A B X D b c h) (@one_cat_native_snake_six_term_result K C C1
  Prod t Add T0 P Q N A B X D b c h))) (@finite_arrow_tail_rest (Functor_cat K C) (@OneCatNativeExactArrowPair K
  C (@additive_preadditive C Prod t Add) C1 t (@additive_terminal_object C Prod t Add) T0 P Q N) (succ (succ
  zero)) (@kernel_adjunction_family_func K C (@additive_preadditive C Prod t Add) t (@additive_terminal_object C
  Prod t Add) P (@transf_arrow_diagram_func K C B X b)) (@finite_arrow_tail_next (Functor_cat K C)
  (@OneCatNativeExactArrowPair K C (@additive_preadditive C Prod t Add) C1 t (@additive_terminal_object C Prod t
  Add) T0 P Q N) (succ (succ (succ zero))) (@kernel_adjunction_family_func K C (@additive_preadditive C Prod t
  Add) t (@additive_terminal_object C Prod t Add) P (@one_cat_native_snake_alpha_diagram K C
  (@additive_preadditive C Prod t Add) C1 t (@additive_terminal_object C Prod t Add) T0 P A B X D b c h))
  (@kernel_adjunction_family_func K C (@additive_preadditive C Prod t Add) t (@additive_terminal_object C Prod t
  Add) P (@transf_arrow_diagram_func K C B X b)) (@one_cat_native_snake_kernel_first K C (@additive_preadditive
  C Prod t Add) C1 t (@additive_terminal_object C Prod t Add) T0 P Q A B X D b c h)
  (@one_cat_native_snake_six_term_result K C C1 Prod t Add T0 P Q N A B X D b c h)) (@finite_arrow_tail_arrow
  (Functor_cat K C) (@OneCatNativeExactArrowPair K C (@additive_preadditive C Prod t Add) C1 t
  (@additive_terminal_object C Prod t Add) T0 P Q N) (succ (succ (succ zero))) (@kernel_adjunction_family_func K
  C (@additive_preadditive C Prod t Add) t (@additive_terminal_object C Prod t Add) P
  (@one_cat_native_snake_alpha_diagram K C (@additive_preadditive C Prod t Add) C1 t (@additive_terminal_object
  C Prod t Add) T0 P A B X D b c h)) (@kernel_adjunction_family_func K C (@additive_preadditive C Prod t Add) t
  (@additive_terminal_object C Prod t Add) P (@transf_arrow_diagram_func K C B X b))
  (@one_cat_native_snake_kernel_first K C (@additive_preadditive C Prod t Add) C1 t (@additive_terminal_object C
  Prod t Add) T0 P Q A B X D b c h) (@one_cat_native_snake_six_term_result K C C1 Prod t Add T0 P Q N A B X D b
  c h)) (@finite_arrow_tail_rest (Functor_cat K C) (@OneCatNativeExactArrowPair K C (@additive_preadditive C
  Prod t Add) C1 t (@additive_terminal_object C Prod t Add) T0 P Q N) (succ (succ (succ zero)))
  (@kernel_adjunction_family_func K C (@additive_preadditive C Prod t Add) t (@additive_terminal_object C Prod t
  Add) P (@one_cat_native_snake_alpha_diagram K C (@additive_preadditive C Prod t Add) C1 t
  (@additive_terminal_object C Prod t Add) T0 P A B X D b c h)) (@kernel_adjunction_family_func K C
  (@additive_preadditive C Prod t Add) t (@additive_terminal_object C Prod t Add) P (@transf_arrow_diagram_func
  K C B X b)) (@one_cat_native_snake_kernel_first K C (@additive_preadditive C Prod t Add) C1 t
  (@additive_terminal_object C Prod t Add) T0 P Q A B X D b c h) (@one_cat_native_snake_six_term_result K C C1
  Prod t Add T0 P Q N A B X D b c h)))) (@finite_arrow_tail_rest (Functor_cat K C) (@OneCatNativeExactArrowPair
  K C (@additive_preadditive C Prod t Add) C1 t (@additive_terminal_object C Prod t Add) T0 P Q N) (succ zero)
  (@finite_arrow_tail_next (Functor_cat K C) (@OneCatNativeExactArrowPair K C (@additive_preadditive C Prod t
  Add) C1 t (@additive_terminal_object C Prod t Add) T0 P Q N) (succ (succ (succ zero)))
  (@kernel_adjunction_family_func K C (@additive_preadditive C Prod t Add) t (@additive_terminal_object C Prod t
  Add) P (@one_cat_native_snake_alpha_diagram K C (@additive_preadditive C Prod t Add) C1 t
  (@additive_terminal_object C Prod t Add) T0 P A B X D b c h)) (@kernel_adjunction_family_func K C
  (@additive_preadditive C Prod t Add) t (@additive_terminal_object C Prod t Add) P (@transf_arrow_diagram_func
  K C B X b)) (@one_cat_native_snake_kernel_first K C (@additive_preadditive C Prod t Add) C1 t
  (@additive_terminal_object C Prod t Add) T0 P Q A B X D b c h) (@one_cat_native_snake_six_term_result K C C1
  Prod t Add T0 P Q N A B X D b c h)) (@finite_arrow_tail_next (Functor_cat K C) (@OneCatNativeExactArrowPair K
  C (@additive_preadditive C Prod t Add) C1 t (@additive_terminal_object C Prod t Add) T0 P Q N) (succ (succ
  zero)) (@kernel_adjunction_family_func K C (@additive_preadditive C Prod t Add) t (@additive_terminal_object C
  Prod t Add) P (@transf_arrow_diagram_func K C B X b)) (@finite_arrow_tail_next (Functor_cat K C)
  (@OneCatNativeExactArrowPair K C (@additive_preadditive C Prod t Add) C1 t (@additive_terminal_object C Prod t
  Add) T0 P Q N) (succ (succ (succ zero))) (@kernel_adjunction_family_func K C (@additive_preadditive C Prod t
  Add) t (@additive_terminal_object C Prod t Add) P (@one_cat_native_snake_alpha_diagram K C
  (@additive_preadditive C Prod t Add) C1 t (@additive_terminal_object C Prod t Add) T0 P A B X D b c h))
  (@kernel_adjunction_family_func K C (@additive_preadditive C Prod t Add) t (@additive_terminal_object C Prod t
  Add) P (@transf_arrow_diagram_func K C B X b)) (@one_cat_native_snake_kernel_first K C (@additive_preadditive
  C Prod t Add) C1 t (@additive_terminal_object C Prod t Add) T0 P Q A B X D b c h)
  (@one_cat_native_snake_six_term_result K C C1 Prod t Add T0 P Q N A B X D b c h)) (@finite_arrow_tail_arrow
  (Functor_cat K C) (@OneCatNativeExactArrowPair K C (@additive_preadditive C Prod t Add) C1 t
  (@additive_terminal_object C Prod t Add) T0 P Q N) (succ (succ (succ zero))) (@kernel_adjunction_family_func K
  C (@additive_preadditive C Prod t Add) t (@additive_terminal_object C Prod t Add) P
  (@one_cat_native_snake_alpha_diagram K C (@additive_preadditive C Prod t Add) C1 t (@additive_terminal_object
  C Prod t Add) T0 P A B X D b c h)) (@kernel_adjunction_family_func K C (@additive_preadditive C Prod t Add) t
  (@additive_terminal_object C Prod t Add) P (@transf_arrow_diagram_func K C B X b))
  (@one_cat_native_snake_kernel_first K C (@additive_preadditive C Prod t Add) C1 t (@additive_terminal_object C
  Prod t Add) T0 P Q A B X D b c h) (@one_cat_native_snake_six_term_result K C C1 Prod t Add T0 P Q N A B X D b
  c h)) (@finite_arrow_tail_rest (Functor_cat K C) (@OneCatNativeExactArrowPair K C (@additive_preadditive C
  Prod t Add) C1 t (@additive_terminal_object C Prod t Add) T0 P Q N) (succ (succ (succ zero)))
  (@kernel_adjunction_family_func K C (@additive_preadditive C Prod t Add) t (@additive_terminal_object C Prod t
  Add) P (@one_cat_native_snake_alpha_diagram K C (@additive_preadditive C Prod t Add) C1 t
  (@additive_terminal_object C Prod t Add) T0 P A B X D b c h)) (@kernel_adjunction_family_func K C
  (@additive_preadditive C Prod t Add) t (@additive_terminal_object C Prod t Add) P (@transf_arrow_diagram_func
  K C B X b)) (@one_cat_native_snake_kernel_first K C (@additive_preadditive C Prod t Add) C1 t
  (@additive_terminal_object C Prod t Add) T0 P Q A B X D b c h) (@one_cat_native_snake_six_term_result K C C1
  Prod t Add T0 P Q N A B X D b c h))) (@finite_arrow_tail_arrow (Functor_cat K C) (@OneCatNativeExactArrowPair
  K C (@additive_preadditive C Prod t Add) C1 t (@additive_terminal_object C Prod t Add) T0 P Q N) (succ (succ
  zero)) (@kernel_adjunction_family_func K C (@additive_preadditive C Prod t Add) t (@additive_terminal_object C
  Prod t Add) P (@transf_arrow_diagram_func K C B X b)) (@finite_arrow_tail_next (Functor_cat K C)
  (@OneCatNativeExactArrowPair K C (@additive_preadditive C Prod t Add) C1 t (@additive_terminal_object C Prod t
  Add) T0 P Q N) (succ (succ (succ zero))) (@kernel_adjunction_family_func K C (@additive_preadditive C Prod t
  Add) t (@additive_terminal_object C Prod t Add) P (@one_cat_native_snake_alpha_diagram K C
  (@additive_preadditive C Prod t Add) C1 t (@additive_terminal_object C Prod t Add) T0 P A B X D b c h))
  (@kernel_adjunction_family_func K C (@additive_preadditive C Prod t Add) t (@additive_terminal_object C Prod t
  Add) P (@transf_arrow_diagram_func K C B X b)) (@one_cat_native_snake_kernel_first K C (@additive_preadditive
  C Prod t Add) C1 t (@additive_terminal_object C Prod t Add) T0 P Q A B X D b c h)
  (@one_cat_native_snake_six_term_result K C C1 Prod t Add T0 P Q N A B X D b c h)) (@finite_arrow_tail_arrow
  (Functor_cat K C) (@OneCatNativeExactArrowPair K C (@additive_preadditive C Prod t Add) C1 t
  (@additive_terminal_object C Prod t Add) T0 P Q N) (succ (succ (succ zero))) (@kernel_adjunction_family_func K
  C (@additive_preadditive C Prod t Add) t (@additive_terminal_object C Prod t Add) P
  (@one_cat_native_snake_alpha_diagram K C (@additive_preadditive C Prod t Add) C1 t (@additive_terminal_object
  C Prod t Add) T0 P A B X D b c h)) (@kernel_adjunction_family_func K C (@additive_preadditive C Prod t Add) t
  (@additive_terminal_object C Prod t Add) P (@transf_arrow_diagram_func K C B X b))
  (@one_cat_native_snake_kernel_first K C (@additive_preadditive C Prod t Add) C1 t (@additive_terminal_object C
  Prod t Add) T0 P Q A B X D b c h) (@one_cat_native_snake_six_term_result K C C1 Prod t Add T0 P Q N A B X D b
  c h)) (@finite_arrow_tail_rest (Functor_cat K C) (@OneCatNativeExactArrowPair K C (@additive_preadditive C
  Prod t Add) C1 t (@additive_terminal_object C Prod t Add) T0 P Q N) (succ (succ (succ zero)))
  (@kernel_adjunction_family_func K C (@additive_preadditive C Prod t Add) t (@additive_terminal_object C Prod t
  Add) P (@one_cat_native_snake_alpha_diagram K C (@additive_preadditive C Prod t Add) C1 t
  (@additive_terminal_object C Prod t Add) T0 P A B X D b c h)) (@kernel_adjunction_family_func K C
  (@additive_preadditive C Prod t Add) t (@additive_terminal_object C Prod t Add) P (@transf_arrow_diagram_func
  K C B X b)) (@one_cat_native_snake_kernel_first K C (@additive_preadditive C Prod t Add) C1 t
  (@additive_terminal_object C Prod t Add) T0 P Q A B X D b c h) (@one_cat_native_snake_six_term_result K C C1
  Prod t Add T0 P Q N A B X D b c h))) (@finite_arrow_tail_rest (Functor_cat K C) (@OneCatNativeExactArrowPair K
  C (@additive_preadditive C Prod t Add) C1 t (@additive_terminal_object C Prod t Add) T0 P Q N) (succ (succ
  zero)) (@kernel_adjunction_family_func K C (@additive_preadditive C Prod t Add) t (@additive_terminal_object C
  Prod t Add) P (@transf_arrow_diagram_func K C B X b)) (@finite_arrow_tail_next (Functor_cat K C)
  (@OneCatNativeExactArrowPair K C (@additive_preadditive C Prod t Add) C1 t (@additive_terminal_object C Prod t
  Add) T0 P Q N) (succ (succ (succ zero))) (@kernel_adjunction_family_func K C (@additive_preadditive C Prod t
  Add) t (@additive_terminal_object C Prod t Add) P (@one_cat_native_snake_alpha_diagram K C
  (@additive_preadditive C Prod t Add) C1 t (@additive_terminal_object C Prod t Add) T0 P A B X D b c h))
  (@kernel_adjunction_family_func K C (@additive_preadditive C Prod t Add) t (@additive_terminal_object C Prod t
  Add) P (@transf_arrow_diagram_func K C B X b)) (@one_cat_native_snake_kernel_first K C (@additive_preadditive
  C Prod t Add) C1 t (@additive_terminal_object C Prod t Add) T0 P Q A B X D b c h)
  (@one_cat_native_snake_six_term_result K C C1 Prod t Add T0 P Q N A B X D b c h)) (@finite_arrow_tail_arrow
  (Functor_cat K C) (@OneCatNativeExactArrowPair K C (@additive_preadditive C Prod t Add) C1 t
  (@additive_terminal_object C Prod t Add) T0 P Q N) (succ (succ (succ zero))) (@kernel_adjunction_family_func K
  C (@additive_preadditive C Prod t Add) t (@additive_terminal_object C Prod t Add) P
  (@one_cat_native_snake_alpha_diagram K C (@additive_preadditive C Prod t Add) C1 t (@additive_terminal_object
  C Prod t Add) T0 P A B X D b c h)) (@kernel_adjunction_family_func K C (@additive_preadditive C Prod t Add) t
  (@additive_terminal_object C Prod t Add) P (@transf_arrow_diagram_func K C B X b))
  (@one_cat_native_snake_kernel_first K C (@additive_preadditive C Prod t Add) C1 t (@additive_terminal_object C
  Prod t Add) T0 P Q A B X D b c h) (@one_cat_native_snake_six_term_result K C C1 Prod t Add T0 P Q N A B X D b
  c h)) (@finite_arrow_tail_rest (Functor_cat K C) (@OneCatNativeExactArrowPair K C (@additive_preadditive C
  Prod t Add) C1 t (@additive_terminal_object C Prod t Add) T0 P Q N) (succ (succ (succ zero)))
  (@kernel_adjunction_family_func K C (@additive_preadditive C Prod t Add) t (@additive_terminal_object C Prod t
  Add) P (@one_cat_native_snake_alpha_diagram K C (@additive_preadditive C Prod t Add) C1 t
  (@additive_terminal_object C Prod t Add) T0 P A B X D b c h)) (@kernel_adjunction_family_func K C
  (@additive_preadditive C Prod t Add) t (@additive_terminal_object C Prod t Add) P (@transf_arrow_diagram_func
  K C B X b)) (@one_cat_native_snake_kernel_first K C (@additive_preadditive C Prod t Add) C1 t
  (@additive_terminal_object C Prod t Add) T0 P Q A B X D b c h) (@one_cat_native_snake_six_term_result K C C1
  Prod t Add T0 P Q N A B X D b c h))))) (@finite_arrow_tail_step (Functor_cat K C) (@OneCatNativeExactArrowPair
  K C (@additive_preadditive C Prod t Add) C1 t (@additive_terminal_object C Prod t Add) T0 P Q N) zero
  (@finite_arrow_tail_next (Functor_cat K C) (@OneCatNativeExactArrowPair K C (@additive_preadditive C Prod t
  Add) C1 t (@additive_terminal_object C Prod t Add) T0 P Q N) (succ (succ zero))
  (@kernel_adjunction_family_func K C (@additive_preadditive C Prod t Add) t (@additive_terminal_object C Prod t
  Add) P (@transf_arrow_diagram_func K C B X b)) (@finite_arrow_tail_next (Functor_cat K C)
  (@OneCatNativeExactArrowPair K C (@additive_preadditive C Prod t Add) C1 t (@additive_terminal_object C Prod t
  Add) T0 P Q N) (succ (succ (succ zero))) (@kernel_adjunction_family_func K C (@additive_preadditive C Prod t
  Add) t (@additive_terminal_object C Prod t Add) P (@one_cat_native_snake_alpha_diagram K C
  (@additive_preadditive C Prod t Add) C1 t (@additive_terminal_object C Prod t Add) T0 P A B X D b c h))
  (@kernel_adjunction_family_func K C (@additive_preadditive C Prod t Add) t (@additive_terminal_object C Prod t
  Add) P (@transf_arrow_diagram_func K C B X b)) (@one_cat_native_snake_kernel_first K C (@additive_preadditive
  C Prod t Add) C1 t (@additive_terminal_object C Prod t Add) T0 P Q A B X D b c h)
  (@one_cat_native_snake_six_term_result K C C1 Prod t Add T0 P Q N A B X D b c h)) (@finite_arrow_tail_arrow
  (Functor_cat K C) (@OneCatNativeExactArrowPair K C (@additive_preadditive C Prod t Add) C1 t
  (@additive_terminal_object C Prod t Add) T0 P Q N) (succ (succ (succ zero))) (@kernel_adjunction_family_func K
  C (@additive_preadditive C Prod t Add) t (@additive_terminal_object C Prod t Add) P
  (@one_cat_native_snake_alpha_diagram K C (@additive_preadditive C Prod t Add) C1 t (@additive_terminal_object
  C Prod t Add) T0 P A B X D b c h)) (@kernel_adjunction_family_func K C (@additive_preadditive C Prod t Add) t
  (@additive_terminal_object C Prod t Add) P (@transf_arrow_diagram_func K C B X b))
  (@one_cat_native_snake_kernel_first K C (@additive_preadditive C Prod t Add) C1 t (@additive_terminal_object C
  Prod t Add) T0 P Q A B X D b c h) (@one_cat_native_snake_six_term_result K C C1 Prod t Add T0 P Q N A B X D b
  c h)) (@finite_arrow_tail_rest (Functor_cat K C) (@OneCatNativeExactArrowPair K C (@additive_preadditive C
  Prod t Add) C1 t (@additive_terminal_object C Prod t Add) T0 P Q N) (succ (succ (succ zero)))
  (@kernel_adjunction_family_func K C (@additive_preadditive C Prod t Add) t (@additive_terminal_object C Prod t
  Add) P (@one_cat_native_snake_alpha_diagram K C (@additive_preadditive C Prod t Add) C1 t
  (@additive_terminal_object C Prod t Add) T0 P A B X D b c h)) (@kernel_adjunction_family_func K C
  (@additive_preadditive C Prod t Add) t (@additive_terminal_object C Prod t Add) P (@transf_arrow_diagram_func
  K C B X b)) (@one_cat_native_snake_kernel_first K C (@additive_preadditive C Prod t Add) C1 t
  (@additive_terminal_object C Prod t Add) T0 P Q A B X D b c h) (@one_cat_native_snake_six_term_result K C C1
  Prod t Add T0 P Q N A B X D b c h))) (@finite_arrow_tail_next (Functor_cat K C) (@OneCatNativeExactArrowPair K
  C (@additive_preadditive C Prod t Add) C1 t (@additive_terminal_object C Prod t Add) T0 P Q N) (succ zero)
  (@finite_arrow_tail_next (Functor_cat K C) (@OneCatNativeExactArrowPair K C (@additive_preadditive C Prod t
  Add) C1 t (@additive_terminal_object C Prod t Add) T0 P Q N) (succ (succ (succ zero)))
  (@kernel_adjunction_family_func K C (@additive_preadditive C Prod t Add) t (@additive_terminal_object C Prod t
  Add) P (@one_cat_native_snake_alpha_diagram K C (@additive_preadditive C Prod t Add) C1 t
  (@additive_terminal_object C Prod t Add) T0 P A B X D b c h)) (@kernel_adjunction_family_func K C
  (@additive_preadditive C Prod t Add) t (@additive_terminal_object C Prod t Add) P (@transf_arrow_diagram_func
  K C B X b)) (@one_cat_native_snake_kernel_first K C (@additive_preadditive C Prod t Add) C1 t
  (@additive_terminal_object C Prod t Add) T0 P Q A B X D b c h) (@one_cat_native_snake_six_term_result K C C1
  Prod t Add T0 P Q N A B X D b c h)) (@finite_arrow_tail_next (Functor_cat K C) (@OneCatNativeExactArrowPair K
  C (@additive_preadditive C Prod t Add) C1 t (@additive_terminal_object C Prod t Add) T0 P Q N) (succ (succ
  zero)) (@kernel_adjunction_family_func K C (@additive_preadditive C Prod t Add) t (@additive_terminal_object C
  Prod t Add) P (@transf_arrow_diagram_func K C B X b)) (@finite_arrow_tail_next (Functor_cat K C)
  (@OneCatNativeExactArrowPair K C (@additive_preadditive C Prod t Add) C1 t (@additive_terminal_object C Prod t
  Add) T0 P Q N) (succ (succ (succ zero))) (@kernel_adjunction_family_func K C (@additive_preadditive C Prod t
  Add) t (@additive_terminal_object C Prod t Add) P (@one_cat_native_snake_alpha_diagram K C
  (@additive_preadditive C Prod t Add) C1 t (@additive_terminal_object C Prod t Add) T0 P A B X D b c h))
  (@kernel_adjunction_family_func K C (@additive_preadditive C Prod t Add) t (@additive_terminal_object C Prod t
  Add) P (@transf_arrow_diagram_func K C B X b)) (@one_cat_native_snake_kernel_first K C (@additive_preadditive
  C Prod t Add) C1 t (@additive_terminal_object C Prod t Add) T0 P Q A B X D b c h)
  (@one_cat_native_snake_six_term_result K C C1 Prod t Add T0 P Q N A B X D b c h)) (@finite_arrow_tail_arrow
  (Functor_cat K C) (@OneCatNativeExactArrowPair K C (@additive_preadditive C Prod t Add) C1 t
  (@additive_terminal_object C Prod t Add) T0 P Q N) (succ (succ (succ zero))) (@kernel_adjunction_family_func K
  C (@additive_preadditive C Prod t Add) t (@additive_terminal_object C Prod t Add) P
  (@one_cat_native_snake_alpha_diagram K C (@additive_preadditive C Prod t Add) C1 t (@additive_terminal_object
  C Prod t Add) T0 P A B X D b c h)) (@kernel_adjunction_family_func K C (@additive_preadditive C Prod t Add) t
  (@additive_terminal_object C Prod t Add) P (@transf_arrow_diagram_func K C B X b))
  (@one_cat_native_snake_kernel_first K C (@additive_preadditive C Prod t Add) C1 t (@additive_terminal_object C
  Prod t Add) T0 P Q A B X D b c h) (@one_cat_native_snake_six_term_result K C C1 Prod t Add T0 P Q N A B X D b
  c h)) (@finite_arrow_tail_rest (Functor_cat K C) (@OneCatNativeExactArrowPair K C (@additive_preadditive C
  Prod t Add) C1 t (@additive_terminal_object C Prod t Add) T0 P Q N) (succ (succ (succ zero)))
  (@kernel_adjunction_family_func K C (@additive_preadditive C Prod t Add) t (@additive_terminal_object C Prod t
  Add) P (@one_cat_native_snake_alpha_diagram K C (@additive_preadditive C Prod t Add) C1 t
  (@additive_terminal_object C Prod t Add) T0 P A B X D b c h)) (@kernel_adjunction_family_func K C
  (@additive_preadditive C Prod t Add) t (@additive_terminal_object C Prod t Add) P (@transf_arrow_diagram_func
  K C B X b)) (@one_cat_native_snake_kernel_first K C (@additive_preadditive C Prod t Add) C1 t
  (@additive_terminal_object C Prod t Add) T0 P Q A B X D b c h) (@one_cat_native_snake_six_term_result K C C1
  Prod t Add T0 P Q N A B X D b c h))) (@finite_arrow_tail_arrow (Functor_cat K C) (@OneCatNativeExactArrowPair
  K C (@additive_preadditive C Prod t Add) C1 t (@additive_terminal_object C Prod t Add) T0 P Q N) (succ (succ
  zero)) (@kernel_adjunction_family_func K C (@additive_preadditive C Prod t Add) t (@additive_terminal_object C
  Prod t Add) P (@transf_arrow_diagram_func K C B X b)) (@finite_arrow_tail_next (Functor_cat K C)
  (@OneCatNativeExactArrowPair K C (@additive_preadditive C Prod t Add) C1 t (@additive_terminal_object C Prod t
  Add) T0 P Q N) (succ (succ (succ zero))) (@kernel_adjunction_family_func K C (@additive_preadditive C Prod t
  Add) t (@additive_terminal_object C Prod t Add) P (@one_cat_native_snake_alpha_diagram K C
  (@additive_preadditive C Prod t Add) C1 t (@additive_terminal_object C Prod t Add) T0 P A B X D b c h))
  (@kernel_adjunction_family_func K C (@additive_preadditive C Prod t Add) t (@additive_terminal_object C Prod t
  Add) P (@transf_arrow_diagram_func K C B X b)) (@one_cat_native_snake_kernel_first K C (@additive_preadditive
  C Prod t Add) C1 t (@additive_terminal_object C Prod t Add) T0 P Q A B X D b c h)
  (@one_cat_native_snake_six_term_result K C C1 Prod t Add T0 P Q N A B X D b c h)) (@finite_arrow_tail_arrow
  (Functor_cat K C) (@OneCatNativeExactArrowPair K C (@additive_preadditive C Prod t Add) C1 t
  (@additive_terminal_object C Prod t Add) T0 P Q N) (succ (succ (succ zero))) (@kernel_adjunction_family_func K
  C (@additive_preadditive C Prod t Add) t (@additive_terminal_object C Prod t Add) P
  (@one_cat_native_snake_alpha_diagram K C (@additive_preadditive C Prod t Add) C1 t (@additive_terminal_object
  C Prod t Add) T0 P A B X D b c h)) (@kernel_adjunction_family_func K C (@additive_preadditive C Prod t Add) t
  (@additive_terminal_object C Prod t Add) P (@transf_arrow_diagram_func K C B X b))
  (@one_cat_native_snake_kernel_first K C (@additive_preadditive C Prod t Add) C1 t (@additive_terminal_object C
  Prod t Add) T0 P Q A B X D b c h) (@one_cat_native_snake_six_term_result K C C1 Prod t Add T0 P Q N A B X D b
  c h)) (@finite_arrow_tail_rest (Functor_cat K C) (@OneCatNativeExactArrowPair K C (@additive_preadditive C
  Prod t Add) C1 t (@additive_terminal_object C Prod t Add) T0 P Q N) (succ (succ (succ zero)))
  (@kernel_adjunction_family_func K C (@additive_preadditive C Prod t Add) t (@additive_terminal_object C Prod t
  Add) P (@one_cat_native_snake_alpha_diagram K C (@additive_preadditive C Prod t Add) C1 t
  (@additive_terminal_object C Prod t Add) T0 P A B X D b c h)) (@kernel_adjunction_family_func K C
  (@additive_preadditive C Prod t Add) t (@additive_terminal_object C Prod t Add) P (@transf_arrow_diagram_func
  K C B X b)) (@one_cat_native_snake_kernel_first K C (@additive_preadditive C Prod t Add) C1 t
  (@additive_terminal_object C Prod t Add) T0 P Q A B X D b c h) (@one_cat_native_snake_six_term_result K C C1
  Prod t Add T0 P Q N A B X D b c h))) (@finite_arrow_tail_rest (Functor_cat K C) (@OneCatNativeExactArrowPair K
  C (@additive_preadditive C Prod t Add) C1 t (@additive_terminal_object C Prod t Add) T0 P Q N) (succ (succ
  zero)) (@kernel_adjunction_family_func K C (@additive_preadditive C Prod t Add) t (@additive_terminal_object C
  Prod t Add) P (@transf_arrow_diagram_func K C B X b)) (@finite_arrow_tail_next (Functor_cat K C)
  (@OneCatNativeExactArrowPair K C (@additive_preadditive C Prod t Add) C1 t (@additive_terminal_object C Prod t
  Add) T0 P Q N) (succ (succ (succ zero))) (@kernel_adjunction_family_func K C (@additive_preadditive C Prod t
  Add) t (@additive_terminal_object C Prod t Add) P (@one_cat_native_snake_alpha_diagram K C
  (@additive_preadditive C Prod t Add) C1 t (@additive_terminal_object C Prod t Add) T0 P A B X D b c h))
  (@kernel_adjunction_family_func K C (@additive_preadditive C Prod t Add) t (@additive_terminal_object C Prod t
  Add) P (@transf_arrow_diagram_func K C B X b)) (@one_cat_native_snake_kernel_first K C (@additive_preadditive
  C Prod t Add) C1 t (@additive_terminal_object C Prod t Add) T0 P Q A B X D b c h)
  (@one_cat_native_snake_six_term_result K C C1 Prod t Add T0 P Q N A B X D b c h)) (@finite_arrow_tail_arrow
  (Functor_cat K C) (@OneCatNativeExactArrowPair K C (@additive_preadditive C Prod t Add) C1 t
  (@additive_terminal_object C Prod t Add) T0 P Q N) (succ (succ (succ zero))) (@kernel_adjunction_family_func K
  C (@additive_preadditive C Prod t Add) t (@additive_terminal_object C Prod t Add) P
  (@one_cat_native_snake_alpha_diagram K C (@additive_preadditive C Prod t Add) C1 t (@additive_terminal_object
  C Prod t Add) T0 P A B X D b c h)) (@kernel_adjunction_family_func K C (@additive_preadditive C Prod t Add) t
  (@additive_terminal_object C Prod t Add) P (@transf_arrow_diagram_func K C B X b))
  (@one_cat_native_snake_kernel_first K C (@additive_preadditive C Prod t Add) C1 t (@additive_terminal_object C
  Prod t Add) T0 P Q A B X D b c h) (@one_cat_native_snake_six_term_result K C C1 Prod t Add T0 P Q N A B X D b
  c h)) (@finite_arrow_tail_rest (Functor_cat K C) (@OneCatNativeExactArrowPair K C (@additive_preadditive C
  Prod t Add) C1 t (@additive_terminal_object C Prod t Add) T0 P Q N) (succ (succ (succ zero)))
  (@kernel_adjunction_family_func K C (@additive_preadditive C Prod t Add) t (@additive_terminal_object C Prod t
  Add) P (@one_cat_native_snake_alpha_diagram K C (@additive_preadditive C Prod t Add) C1 t
  (@additive_terminal_object C Prod t Add) T0 P A B X D b c h)) (@kernel_adjunction_family_func K C
  (@additive_preadditive C Prod t Add) t (@additive_terminal_object C Prod t Add) P (@transf_arrow_diagram_func
  K C B X b)) (@one_cat_native_snake_kernel_first K C (@additive_preadditive C Prod t Add) C1 t
  (@additive_terminal_object C Prod t Add) T0 P Q A B X D b c h) (@one_cat_native_snake_six_term_result K C C1
  Prod t Add T0 P Q N A B X D b c h)))) (@finite_arrow_tail_arrow (Functor_cat K C) (@OneCatNativeExactArrowPair
  K C (@additive_preadditive C Prod t Add) C1 t (@additive_terminal_object C Prod t Add) T0 P Q N) (succ zero)
  (@finite_arrow_tail_next (Functor_cat K C) (@OneCatNativeExactArrowPair K C (@additive_preadditive C Prod t
  Add) C1 t (@additive_terminal_object C Prod t Add) T0 P Q N) (succ (succ (succ zero)))
  (@kernel_adjunction_family_func K C (@additive_preadditive C Prod t Add) t (@additive_terminal_object C Prod t
  Add) P (@one_cat_native_snake_alpha_diagram K C (@additive_preadditive C Prod t Add) C1 t
  (@additive_terminal_object C Prod t Add) T0 P A B X D b c h)) (@kernel_adjunction_family_func K C
  (@additive_preadditive C Prod t Add) t (@additive_terminal_object C Prod t Add) P (@transf_arrow_diagram_func
  K C B X b)) (@one_cat_native_snake_kernel_first K C (@additive_preadditive C Prod t Add) C1 t
  (@additive_terminal_object C Prod t Add) T0 P Q A B X D b c h) (@one_cat_native_snake_six_term_result K C C1
  Prod t Add T0 P Q N A B X D b c h)) (@finite_arrow_tail_next (Functor_cat K C) (@OneCatNativeExactArrowPair K
  C (@additive_preadditive C Prod t Add) C1 t (@additive_terminal_object C Prod t Add) T0 P Q N) (succ (succ
  zero)) (@kernel_adjunction_family_func K C (@additive_preadditive C Prod t Add) t (@additive_terminal_object C
  Prod t Add) P (@transf_arrow_diagram_func K C B X b)) (@finite_arrow_tail_next (Functor_cat K C)
  (@OneCatNativeExactArrowPair K C (@additive_preadditive C Prod t Add) C1 t (@additive_terminal_object C Prod t
  Add) T0 P Q N) (succ (succ (succ zero))) (@kernel_adjunction_family_func K C (@additive_preadditive C Prod t
  Add) t (@additive_terminal_object C Prod t Add) P (@one_cat_native_snake_alpha_diagram K C
  (@additive_preadditive C Prod t Add) C1 t (@additive_terminal_object C Prod t Add) T0 P A B X D b c h))
  (@kernel_adjunction_family_func K C (@additive_preadditive C Prod t Add) t (@additive_terminal_object C Prod t
  Add) P (@transf_arrow_diagram_func K C B X b)) (@one_cat_native_snake_kernel_first K C (@additive_preadditive
  C Prod t Add) C1 t (@additive_terminal_object C Prod t Add) T0 P Q A B X D b c h)
  (@one_cat_native_snake_six_term_result K C C1 Prod t Add T0 P Q N A B X D b c h)) (@finite_arrow_tail_arrow
  (Functor_cat K C) (@OneCatNativeExactArrowPair K C (@additive_preadditive C Prod t Add) C1 t
  (@additive_terminal_object C Prod t Add) T0 P Q N) (succ (succ (succ zero))) (@kernel_adjunction_family_func K
  C (@additive_preadditive C Prod t Add) t (@additive_terminal_object C Prod t Add) P
  (@one_cat_native_snake_alpha_diagram K C (@additive_preadditive C Prod t Add) C1 t (@additive_terminal_object
  C Prod t Add) T0 P A B X D b c h)) (@kernel_adjunction_family_func K C (@additive_preadditive C Prod t Add) t
  (@additive_terminal_object C Prod t Add) P (@transf_arrow_diagram_func K C B X b))
  (@one_cat_native_snake_kernel_first K C (@additive_preadditive C Prod t Add) C1 t (@additive_terminal_object C
  Prod t Add) T0 P Q A B X D b c h) (@one_cat_native_snake_six_term_result K C C1 Prod t Add T0 P Q N A B X D b
  c h)) (@finite_arrow_tail_rest (Functor_cat K C) (@OneCatNativeExactArrowPair K C (@additive_preadditive C
  Prod t Add) C1 t (@additive_terminal_object C Prod t Add) T0 P Q N) (succ (succ (succ zero)))
  (@kernel_adjunction_family_func K C (@additive_preadditive C Prod t Add) t (@additive_terminal_object C Prod t
  Add) P (@one_cat_native_snake_alpha_diagram K C (@additive_preadditive C Prod t Add) C1 t
  (@additive_terminal_object C Prod t Add) T0 P A B X D b c h)) (@kernel_adjunction_family_func K C
  (@additive_preadditive C Prod t Add) t (@additive_terminal_object C Prod t Add) P (@transf_arrow_diagram_func
  K C B X b)) (@one_cat_native_snake_kernel_first K C (@additive_preadditive C Prod t Add) C1 t
  (@additive_terminal_object C Prod t Add) T0 P Q A B X D b c h) (@one_cat_native_snake_six_term_result K C C1
  Prod t Add T0 P Q N A B X D b c h))) (@finite_arrow_tail_arrow (Functor_cat K C) (@OneCatNativeExactArrowPair
  K C (@additive_preadditive C Prod t Add) C1 t (@additive_terminal_object C Prod t Add) T0 P Q N) (succ (succ
  zero)) (@kernel_adjunction_family_func K C (@additive_preadditive C Prod t Add) t (@additive_terminal_object C
  Prod t Add) P (@transf_arrow_diagram_func K C B X b)) (@finite_arrow_tail_next (Functor_cat K C)
  (@OneCatNativeExactArrowPair K C (@additive_preadditive C Prod t Add) C1 t (@additive_terminal_object C Prod t
  Add) T0 P Q N) (succ (succ (succ zero))) (@kernel_adjunction_family_func K C (@additive_preadditive C Prod t
  Add) t (@additive_terminal_object C Prod t Add) P (@one_cat_native_snake_alpha_diagram K C
  (@additive_preadditive C Prod t Add) C1 t (@additive_terminal_object C Prod t Add) T0 P A B X D b c h))
  (@kernel_adjunction_family_func K C (@additive_preadditive C Prod t Add) t (@additive_terminal_object C Prod t
  Add) P (@transf_arrow_diagram_func K C B X b)) (@one_cat_native_snake_kernel_first K C (@additive_preadditive
  C Prod t Add) C1 t (@additive_terminal_object C Prod t Add) T0 P Q A B X D b c h)
  (@one_cat_native_snake_six_term_result K C C1 Prod t Add T0 P Q N A B X D b c h)) (@finite_arrow_tail_arrow
  (Functor_cat K C) (@OneCatNativeExactArrowPair K C (@additive_preadditive C Prod t Add) C1 t
  (@additive_terminal_object C Prod t Add) T0 P Q N) (succ (succ (succ zero))) (@kernel_adjunction_family_func K
  C (@additive_preadditive C Prod t Add) t (@additive_terminal_object C Prod t Add) P
  (@one_cat_native_snake_alpha_diagram K C (@additive_preadditive C Prod t Add) C1 t (@additive_terminal_object
  C Prod t Add) T0 P A B X D b c h)) (@kernel_adjunction_family_func K C (@additive_preadditive C Prod t Add) t
  (@additive_terminal_object C Prod t Add) P (@transf_arrow_diagram_func K C B X b))
  (@one_cat_native_snake_kernel_first K C (@additive_preadditive C Prod t Add) C1 t (@additive_terminal_object C
  Prod t Add) T0 P Q A B X D b c h) (@one_cat_native_snake_six_term_result K C C1 Prod t Add T0 P Q N A B X D b
  c h)) (@finite_arrow_tail_rest (Functor_cat K C) (@OneCatNativeExactArrowPair K C (@additive_preadditive C
  Prod t Add) C1 t (@additive_terminal_object C Prod t Add) T0 P Q N) (succ (succ (succ zero)))
  (@kernel_adjunction_family_func K C (@additive_preadditive C Prod t Add) t (@additive_terminal_object C Prod t
  Add) P (@one_cat_native_snake_alpha_diagram K C (@additive_preadditive C Prod t Add) C1 t
  (@additive_terminal_object C Prod t Add) T0 P A B X D b c h)) (@kernel_adjunction_family_func K C
  (@additive_preadditive C Prod t Add) t (@additive_terminal_object C Prod t Add) P (@transf_arrow_diagram_func
  K C B X b)) (@one_cat_native_snake_kernel_first K C (@additive_preadditive C Prod t Add) C1 t
  (@additive_terminal_object C Prod t Add) T0 P Q A B X D b c h) (@one_cat_native_snake_six_term_result K C C1
  Prod t Add T0 P Q N A B X D b c h))) (@finite_arrow_tail_rest (Functor_cat K C) (@OneCatNativeExactArrowPair K
  C (@additive_preadditive C Prod t Add) C1 t (@additive_terminal_object C Prod t Add) T0 P Q N) (succ (succ
  zero)) (@kernel_adjunction_family_func K C (@additive_preadditive C Prod t Add) t (@additive_terminal_object C
  Prod t Add) P (@transf_arrow_diagram_func K C B X b)) (@finite_arrow_tail_next (Functor_cat K C)
  (@OneCatNativeExactArrowPair K C (@additive_preadditive C Prod t Add) C1 t (@additive_terminal_object C Prod t
  Add) T0 P Q N) (succ (succ (succ zero))) (@kernel_adjunction_family_func K C (@additive_preadditive C Prod t
  Add) t (@additive_terminal_object C Prod t Add) P (@one_cat_native_snake_alpha_diagram K C
  (@additive_preadditive C Prod t Add) C1 t (@additive_terminal_object C Prod t Add) T0 P A B X D b c h))
  (@kernel_adjunction_family_func K C (@additive_preadditive C Prod t Add) t (@additive_terminal_object C Prod t
  Add) P (@transf_arrow_diagram_func K C B X b)) (@one_cat_native_snake_kernel_first K C (@additive_preadditive
  C Prod t Add) C1 t (@additive_terminal_object C Prod t Add) T0 P Q A B X D b c h)
  (@one_cat_native_snake_six_term_result K C C1 Prod t Add T0 P Q N A B X D b c h)) (@finite_arrow_tail_arrow
  (Functor_cat K C) (@OneCatNativeExactArrowPair K C (@additive_preadditive C Prod t Add) C1 t
  (@additive_terminal_object C Prod t Add) T0 P Q N) (succ (succ (succ zero))) (@kernel_adjunction_family_func K
  C (@additive_preadditive C Prod t Add) t (@additive_terminal_object C Prod t Add) P
  (@one_cat_native_snake_alpha_diagram K C (@additive_preadditive C Prod t Add) C1 t (@additive_terminal_object
  C Prod t Add) T0 P A B X D b c h)) (@kernel_adjunction_family_func K C (@additive_preadditive C Prod t Add) t
  (@additive_terminal_object C Prod t Add) P (@transf_arrow_diagram_func K C B X b))
  (@one_cat_native_snake_kernel_first K C (@additive_preadditive C Prod t Add) C1 t (@additive_terminal_object C
  Prod t Add) T0 P Q A B X D b c h) (@one_cat_native_snake_six_term_result K C C1 Prod t Add T0 P Q N A B X D b
  c h)) (@finite_arrow_tail_rest (Functor_cat K C) (@OneCatNativeExactArrowPair K C (@additive_preadditive C
  Prod t Add) C1 t (@additive_terminal_object C Prod t Add) T0 P Q N) (succ (succ (succ zero)))
  (@kernel_adjunction_family_func K C (@additive_preadditive C Prod t Add) t (@additive_terminal_object C Prod t
  Add) P (@one_cat_native_snake_alpha_diagram K C (@additive_preadditive C Prod t Add) C1 t
  (@additive_terminal_object C Prod t Add) T0 P A B X D b c h)) (@kernel_adjunction_family_func K C
  (@additive_preadditive C Prod t Add) t (@additive_terminal_object C Prod t Add) P (@transf_arrow_diagram_func
  K C B X b)) (@one_cat_native_snake_kernel_first K C (@additive_preadditive C Prod t Add) C1 t
  (@additive_terminal_object C Prod t Add) T0 P Q A B X D b c h) (@one_cat_native_snake_six_term_result K C C1
  Prod t Add T0 P Q N A B X D b c h)))) (@finite_arrow_tail_rest (Functor_cat K C) (@OneCatNativeExactArrowPair
  K C (@additive_preadditive C Prod t Add) C1 t (@additive_terminal_object C Prod t Add) T0 P Q N) (succ zero)
  (@finite_arrow_tail_next (Functor_cat K C) (@OneCatNativeExactArrowPair K C (@additive_preadditive C Prod t
  Add) C1 t (@additive_terminal_object C Prod t Add) T0 P Q N) (succ (succ (succ zero)))
  (@kernel_adjunction_family_func K C (@additive_preadditive C Prod t Add) t (@additive_terminal_object C Prod t
  Add) P (@one_cat_native_snake_alpha_diagram K C (@additive_preadditive C Prod t Add) C1 t
  (@additive_terminal_object C Prod t Add) T0 P A B X D b c h)) (@kernel_adjunction_family_func K C
  (@additive_preadditive C Prod t Add) t (@additive_terminal_object C Prod t Add) P (@transf_arrow_diagram_func
  K C B X b)) (@one_cat_native_snake_kernel_first K C (@additive_preadditive C Prod t Add) C1 t
  (@additive_terminal_object C Prod t Add) T0 P Q A B X D b c h) (@one_cat_native_snake_six_term_result K C C1
  Prod t Add T0 P Q N A B X D b c h)) (@finite_arrow_tail_next (Functor_cat K C) (@OneCatNativeExactArrowPair K
  C (@additive_preadditive C Prod t Add) C1 t (@additive_terminal_object C Prod t Add) T0 P Q N) (succ (succ
  zero)) (@kernel_adjunction_family_func K C (@additive_preadditive C Prod t Add) t (@additive_terminal_object C
  Prod t Add) P (@transf_arrow_diagram_func K C B X b)) (@finite_arrow_tail_next (Functor_cat K C)
  (@OneCatNativeExactArrowPair K C (@additive_preadditive C Prod t Add) C1 t (@additive_terminal_object C Prod t
  Add) T0 P Q N) (succ (succ (succ zero))) (@kernel_adjunction_family_func K C (@additive_preadditive C Prod t
  Add) t (@additive_terminal_object C Prod t Add) P (@one_cat_native_snake_alpha_diagram K C
  (@additive_preadditive C Prod t Add) C1 t (@additive_terminal_object C Prod t Add) T0 P A B X D b c h))
  (@kernel_adjunction_family_func K C (@additive_preadditive C Prod t Add) t (@additive_terminal_object C Prod t
  Add) P (@transf_arrow_diagram_func K C B X b)) (@one_cat_native_snake_kernel_first K C (@additive_preadditive
  C Prod t Add) C1 t (@additive_terminal_object C Prod t Add) T0 P Q A B X D b c h)
  (@one_cat_native_snake_six_term_result K C C1 Prod t Add T0 P Q N A B X D b c h)) (@finite_arrow_tail_arrow
  (Functor_cat K C) (@OneCatNativeExactArrowPair K C (@additive_preadditive C Prod t Add) C1 t
  (@additive_terminal_object C Prod t Add) T0 P Q N) (succ (succ (succ zero))) (@kernel_adjunction_family_func K
  C (@additive_preadditive C Prod t Add) t (@additive_terminal_object C Prod t Add) P
  (@one_cat_native_snake_alpha_diagram K C (@additive_preadditive C Prod t Add) C1 t (@additive_terminal_object
  C Prod t Add) T0 P A B X D b c h)) (@kernel_adjunction_family_func K C (@additive_preadditive C Prod t Add) t
  (@additive_terminal_object C Prod t Add) P (@transf_arrow_diagram_func K C B X b))
  (@one_cat_native_snake_kernel_first K C (@additive_preadditive C Prod t Add) C1 t (@additive_terminal_object C
  Prod t Add) T0 P Q A B X D b c h) (@one_cat_native_snake_six_term_result K C C1 Prod t Add T0 P Q N A B X D b
  c h)) (@finite_arrow_tail_rest (Functor_cat K C) (@OneCatNativeExactArrowPair K C (@additive_preadditive C
  Prod t Add) C1 t (@additive_terminal_object C Prod t Add) T0 P Q N) (succ (succ (succ zero)))
  (@kernel_adjunction_family_func K C (@additive_preadditive C Prod t Add) t (@additive_terminal_object C Prod t
  Add) P (@one_cat_native_snake_alpha_diagram K C (@additive_preadditive C Prod t Add) C1 t
  (@additive_terminal_object C Prod t Add) T0 P A B X D b c h)) (@kernel_adjunction_family_func K C
  (@additive_preadditive C Prod t Add) t (@additive_terminal_object C Prod t Add) P (@transf_arrow_diagram_func
  K C B X b)) (@one_cat_native_snake_kernel_first K C (@additive_preadditive C Prod t Add) C1 t
  (@additive_terminal_object C Prod t Add) T0 P Q A B X D b c h) (@one_cat_native_snake_six_term_result K C C1
  Prod t Add T0 P Q N A B X D b c h))) (@finite_arrow_tail_arrow (Functor_cat K C) (@OneCatNativeExactArrowPair
  K C (@additive_preadditive C Prod t Add) C1 t (@additive_terminal_object C Prod t Add) T0 P Q N) (succ (succ
  zero)) (@kernel_adjunction_family_func K C (@additive_preadditive C Prod t Add) t (@additive_terminal_object C
  Prod t Add) P (@transf_arrow_diagram_func K C B X b)) (@finite_arrow_tail_next (Functor_cat K C)
  (@OneCatNativeExactArrowPair K C (@additive_preadditive C Prod t Add) C1 t (@additive_terminal_object C Prod t
  Add) T0 P Q N) (succ (succ (succ zero))) (@kernel_adjunction_family_func K C (@additive_preadditive C Prod t
  Add) t (@additive_terminal_object C Prod t Add) P (@one_cat_native_snake_alpha_diagram K C
  (@additive_preadditive C Prod t Add) C1 t (@additive_terminal_object C Prod t Add) T0 P A B X D b c h))
  (@kernel_adjunction_family_func K C (@additive_preadditive C Prod t Add) t (@additive_terminal_object C Prod t
  Add) P (@transf_arrow_diagram_func K C B X b)) (@one_cat_native_snake_kernel_first K C (@additive_preadditive
  C Prod t Add) C1 t (@additive_terminal_object C Prod t Add) T0 P Q A B X D b c h)
  (@one_cat_native_snake_six_term_result K C C1 Prod t Add T0 P Q N A B X D b c h)) (@finite_arrow_tail_arrow
  (Functor_cat K C) (@OneCatNativeExactArrowPair K C (@additive_preadditive C Prod t Add) C1 t
  (@additive_terminal_object C Prod t Add) T0 P Q N) (succ (succ (succ zero))) (@kernel_adjunction_family_func K
  C (@additive_preadditive C Prod t Add) t (@additive_terminal_object C Prod t Add) P
  (@one_cat_native_snake_alpha_diagram K C (@additive_preadditive C Prod t Add) C1 t (@additive_terminal_object
  C Prod t Add) T0 P A B X D b c h)) (@kernel_adjunction_family_func K C (@additive_preadditive C Prod t Add) t
  (@additive_terminal_object C Prod t Add) P (@transf_arrow_diagram_func K C B X b))
  (@one_cat_native_snake_kernel_first K C (@additive_preadditive C Prod t Add) C1 t (@additive_terminal_object C
  Prod t Add) T0 P Q A B X D b c h) (@one_cat_native_snake_six_term_result K C C1 Prod t Add T0 P Q N A B X D b
  c h)) (@finite_arrow_tail_rest (Functor_cat K C) (@OneCatNativeExactArrowPair K C (@additive_preadditive C
  Prod t Add) C1 t (@additive_terminal_object C Prod t Add) T0 P Q N) (succ (succ (succ zero)))
  (@kernel_adjunction_family_func K C (@additive_preadditive C Prod t Add) t (@additive_terminal_object C Prod t
  Add) P (@one_cat_native_snake_alpha_diagram K C (@additive_preadditive C Prod t Add) C1 t
  (@additive_terminal_object C Prod t Add) T0 P A B X D b c h)) (@kernel_adjunction_family_func K C
  (@additive_preadditive C Prod t Add) t (@additive_terminal_object C Prod t Add) P (@transf_arrow_diagram_func
  K C B X b)) (@one_cat_native_snake_kernel_first K C (@additive_preadditive C Prod t Add) C1 t
  (@additive_terminal_object C Prod t Add) T0 P Q A B X D b c h) (@one_cat_native_snake_six_term_result K C C1
  Prod t Add T0 P Q N A B X D b c h))) (@finite_arrow_tail_rest (Functor_cat K C) (@OneCatNativeExactArrowPair K
  C (@additive_preadditive C Prod t Add) C1 t (@additive_terminal_object C Prod t Add) T0 P Q N) (succ (succ
  zero)) (@kernel_adjunction_family_func K C (@additive_preadditive C Prod t Add) t (@additive_terminal_object C
  Prod t Add) P (@transf_arrow_diagram_func K C B X b)) (@finite_arrow_tail_next (Functor_cat K C)
  (@OneCatNativeExactArrowPair K C (@additive_preadditive C Prod t Add) C1 t (@additive_terminal_object C Prod t
  Add) T0 P Q N) (succ (succ (succ zero))) (@kernel_adjunction_family_func K C (@additive_preadditive C Prod t
  Add) t (@additive_terminal_object C Prod t Add) P (@one_cat_native_snake_alpha_diagram K C
  (@additive_preadditive C Prod t Add) C1 t (@additive_terminal_object C Prod t Add) T0 P A B X D b c h))
  (@kernel_adjunction_family_func K C (@additive_preadditive C Prod t Add) t (@additive_terminal_object C Prod t
  Add) P (@transf_arrow_diagram_func K C B X b)) (@one_cat_native_snake_kernel_first K C (@additive_preadditive
  C Prod t Add) C1 t (@additive_terminal_object C Prod t Add) T0 P Q A B X D b c h)
  (@one_cat_native_snake_six_term_result K C C1 Prod t Add T0 P Q N A B X D b c h)) (@finite_arrow_tail_arrow
  (Functor_cat K C) (@OneCatNativeExactArrowPair K C (@additive_preadditive C Prod t Add) C1 t
  (@additive_terminal_object C Prod t Add) T0 P Q N) (succ (succ (succ zero))) (@kernel_adjunction_family_func K
  C (@additive_preadditive C Prod t Add) t (@additive_terminal_object C Prod t Add) P
  (@one_cat_native_snake_alpha_diagram K C (@additive_preadditive C Prod t Add) C1 t (@additive_terminal_object
  C Prod t Add) T0 P A B X D b c h)) (@kernel_adjunction_family_func K C (@additive_preadditive C Prod t Add) t
  (@additive_terminal_object C Prod t Add) P (@transf_arrow_diagram_func K C B X b))
  (@one_cat_native_snake_kernel_first K C (@additive_preadditive C Prod t Add) C1 t (@additive_terminal_object C
  Prod t Add) T0 P Q A B X D b c h) (@one_cat_native_snake_six_term_result K C C1 Prod t Add T0 P Q N A B X D b
  c h)) (@finite_arrow_tail_rest (Functor_cat K C) (@OneCatNativeExactArrowPair K C (@additive_preadditive C
  Prod t Add) C1 t (@additive_terminal_object C Prod t Add) T0 P Q N) (succ (succ (succ zero)))
  (@kernel_adjunction_family_func K C (@additive_preadditive C Prod t Add) t (@additive_terminal_object C Prod t
  Add) P (@one_cat_native_snake_alpha_diagram K C (@additive_preadditive C Prod t Add) C1 t
  (@additive_terminal_object C Prod t Add) T0 P A B X D b c h)) (@kernel_adjunction_family_func K C
  (@additive_preadditive C Prod t Add) t (@additive_terminal_object C Prod t Add) P (@transf_arrow_diagram_func
  K C B X b)) (@one_cat_native_snake_kernel_first K C (@additive_preadditive C Prod t Add) C1 t
  (@additive_terminal_object C Prod t Add) T0 P Q A B X D b c h) (@one_cat_native_snake_six_term_result K C C1
  Prod t Add T0 P Q N A B X D b c h))))))
  : τ (@= (@Transf K C (@finite_arrow_tail_next (Functor_cat K C) (@OneCatNativeExactArrowPair K C
  (@additive_preadditive C Prod t Add) C1 t (@additive_terminal_object C Prod t Add) T0 P Q N) (succ (succ
  zero)) (@kernel_adjunction_family_func K C (@additive_preadditive C Prod t Add) t (@additive_terminal_object C
  Prod t Add) P (@transf_arrow_diagram_func K C B X b)) (@finite_arrow_tail_next (Functor_cat K C)
  (@OneCatNativeExactArrowPair K C (@additive_preadditive C Prod t Add) C1 t (@additive_terminal_object C Prod t
  Add) T0 P Q N) (succ (succ (succ zero))) (@kernel_adjunction_family_func K C (@additive_preadditive C Prod t
  Add) t (@additive_terminal_object C Prod t Add) P (@one_cat_native_snake_alpha_diagram K C
  (@additive_preadditive C Prod t Add) C1 t (@additive_terminal_object C Prod t Add) T0 P A B X D b c h))
  (@kernel_adjunction_family_func K C (@additive_preadditive C Prod t Add) t (@additive_terminal_object C Prod t
  Add) P (@transf_arrow_diagram_func K C B X b)) (@one_cat_native_snake_kernel_first K C (@additive_preadditive
  C Prod t Add) C1 t (@additive_terminal_object C Prod t Add) T0 P Q A B X D b c h)
  (@one_cat_native_snake_six_term_result K C C1 Prod t Add T0 P Q N A B X D b c h)) (@finite_arrow_tail_arrow
  (Functor_cat K C) (@OneCatNativeExactArrowPair K C (@additive_preadditive C Prod t Add) C1 t
  (@additive_terminal_object C Prod t Add) T0 P Q N) (succ (succ (succ zero))) (@kernel_adjunction_family_func K
  C (@additive_preadditive C Prod t Add) t (@additive_terminal_object C Prod t Add) P
  (@one_cat_native_snake_alpha_diagram K C (@additive_preadditive C Prod t Add) C1 t (@additive_terminal_object
  C Prod t Add) T0 P A B X D b c h)) (@kernel_adjunction_family_func K C (@additive_preadditive C Prod t Add) t
  (@additive_terminal_object C Prod t Add) P (@transf_arrow_diagram_func K C B X b))
  (@one_cat_native_snake_kernel_first K C (@additive_preadditive C Prod t Add) C1 t (@additive_terminal_object C
  Prod t Add) T0 P Q A B X D b c h) (@one_cat_native_snake_six_term_result K C C1 Prod t Add T0 P Q N A B X D b
  c h)) (@finite_arrow_tail_rest (Functor_cat K C) (@OneCatNativeExactArrowPair K C (@additive_preadditive C
  Prod t Add) C1 t (@additive_terminal_object C Prod t Add) T0 P Q N) (succ (succ (succ zero)))
  (@kernel_adjunction_family_func K C (@additive_preadditive C Prod t Add) t (@additive_terminal_object C Prod t
  Add) P (@one_cat_native_snake_alpha_diagram K C (@additive_preadditive C Prod t Add) C1 t
  (@additive_terminal_object C Prod t Add) T0 P A B X D b c h)) (@kernel_adjunction_family_func K C
  (@additive_preadditive C Prod t Add) t (@additive_terminal_object C Prod t Add) P (@transf_arrow_diagram_func
  K C B X b)) (@one_cat_native_snake_kernel_first K C (@additive_preadditive C Prod t Add) C1 t
  (@additive_terminal_object C Prod t Add) T0 P Q A B X D b c h) (@one_cat_native_snake_six_term_result K C C1
  Prod t Add T0 P Q N A B X D b c h))) (@finite_arrow_tail_next (Functor_cat K C) (@OneCatNativeExactArrowPair K
  C (@additive_preadditive C Prod t Add) C1 t (@additive_terminal_object C Prod t Add) T0 P Q N) zero
  (@finite_arrow_tail_next (Functor_cat K C) (@OneCatNativeExactArrowPair K C (@additive_preadditive C Prod t
  Add) C1 t (@additive_terminal_object C Prod t Add) T0 P Q N) (succ (succ zero))
  (@kernel_adjunction_family_func K C (@additive_preadditive C Prod t Add) t (@additive_terminal_object C Prod t
  Add) P (@transf_arrow_diagram_func K C B X b)) (@finite_arrow_tail_next (Functor_cat K C)
  (@OneCatNativeExactArrowPair K C (@additive_preadditive C Prod t Add) C1 t (@additive_terminal_object C Prod t
  Add) T0 P Q N) (succ (succ (succ zero))) (@kernel_adjunction_family_func K C (@additive_preadditive C Prod t
  Add) t (@additive_terminal_object C Prod t Add) P (@one_cat_native_snake_alpha_diagram K C
  (@additive_preadditive C Prod t Add) C1 t (@additive_terminal_object C Prod t Add) T0 P A B X D b c h))
  (@kernel_adjunction_family_func K C (@additive_preadditive C Prod t Add) t (@additive_terminal_object C Prod t
  Add) P (@transf_arrow_diagram_func K C B X b)) (@one_cat_native_snake_kernel_first K C (@additive_preadditive
  C Prod t Add) C1 t (@additive_terminal_object C Prod t Add) T0 P Q A B X D b c h)
  (@one_cat_native_snake_six_term_result K C C1 Prod t Add T0 P Q N A B X D b c h)) (@finite_arrow_tail_arrow
  (Functor_cat K C) (@OneCatNativeExactArrowPair K C (@additive_preadditive C Prod t Add) C1 t
  (@additive_terminal_object C Prod t Add) T0 P Q N) (succ (succ (succ zero))) (@kernel_adjunction_family_func K
  C (@additive_preadditive C Prod t Add) t (@additive_terminal_object C Prod t Add) P
  (@one_cat_native_snake_alpha_diagram K C (@additive_preadditive C Prod t Add) C1 t (@additive_terminal_object
  C Prod t Add) T0 P A B X D b c h)) (@kernel_adjunction_family_func K C (@additive_preadditive C Prod t Add) t
  (@additive_terminal_object C Prod t Add) P (@transf_arrow_diagram_func K C B X b))
  (@one_cat_native_snake_kernel_first K C (@additive_preadditive C Prod t Add) C1 t (@additive_terminal_object C
  Prod t Add) T0 P Q A B X D b c h) (@one_cat_native_snake_six_term_result K C C1 Prod t Add T0 P Q N A B X D b
  c h)) (@finite_arrow_tail_rest (Functor_cat K C) (@OneCatNativeExactArrowPair K C (@additive_preadditive C
  Prod t Add) C1 t (@additive_terminal_object C Prod t Add) T0 P Q N) (succ (succ (succ zero)))
  (@kernel_adjunction_family_func K C (@additive_preadditive C Prod t Add) t (@additive_terminal_object C Prod t
  Add) P (@one_cat_native_snake_alpha_diagram K C (@additive_preadditive C Prod t Add) C1 t
  (@additive_terminal_object C Prod t Add) T0 P A B X D b c h)) (@kernel_adjunction_family_func K C
  (@additive_preadditive C Prod t Add) t (@additive_terminal_object C Prod t Add) P (@transf_arrow_diagram_func
  K C B X b)) (@one_cat_native_snake_kernel_first K C (@additive_preadditive C Prod t Add) C1 t
  (@additive_terminal_object C Prod t Add) T0 P Q A B X D b c h) (@one_cat_native_snake_six_term_result K C C1
  Prod t Add T0 P Q N A B X D b c h))) (@finite_arrow_tail_next (Functor_cat K C) (@OneCatNativeExactArrowPair K
  C (@additive_preadditive C Prod t Add) C1 t (@additive_terminal_object C Prod t Add) T0 P Q N) (succ zero)
  (@finite_arrow_tail_next (Functor_cat K C) (@OneCatNativeExactArrowPair K C (@additive_preadditive C Prod t
  Add) C1 t (@additive_terminal_object C Prod t Add) T0 P Q N) (succ (succ (succ zero)))
  (@kernel_adjunction_family_func K C (@additive_preadditive C Prod t Add) t (@additive_terminal_object C Prod t
  Add) P (@one_cat_native_snake_alpha_diagram K C (@additive_preadditive C Prod t Add) C1 t
  (@additive_terminal_object C Prod t Add) T0 P A B X D b c h)) (@kernel_adjunction_family_func K C
  (@additive_preadditive C Prod t Add) t (@additive_terminal_object C Prod t Add) P (@transf_arrow_diagram_func
  K C B X b)) (@one_cat_native_snake_kernel_first K C (@additive_preadditive C Prod t Add) C1 t
  (@additive_terminal_object C Prod t Add) T0 P Q A B X D b c h) (@one_cat_native_snake_six_term_result K C C1
  Prod t Add T0 P Q N A B X D b c h)) (@finite_arrow_tail_next (Functor_cat K C) (@OneCatNativeExactArrowPair K
  C (@additive_preadditive C Prod t Add) C1 t (@additive_terminal_object C Prod t Add) T0 P Q N) (succ (succ
  zero)) (@kernel_adjunction_family_func K C (@additive_preadditive C Prod t Add) t (@additive_terminal_object C
  Prod t Add) P (@transf_arrow_diagram_func K C B X b)) (@finite_arrow_tail_next (Functor_cat K C)
  (@OneCatNativeExactArrowPair K C (@additive_preadditive C Prod t Add) C1 t (@additive_terminal_object C Prod t
  Add) T0 P Q N) (succ (succ (succ zero))) (@kernel_adjunction_family_func K C (@additive_preadditive C Prod t
  Add) t (@additive_terminal_object C Prod t Add) P (@one_cat_native_snake_alpha_diagram K C
  (@additive_preadditive C Prod t Add) C1 t (@additive_terminal_object C Prod t Add) T0 P A B X D b c h))
  (@kernel_adjunction_family_func K C (@additive_preadditive C Prod t Add) t (@additive_terminal_object C Prod t
  Add) P (@transf_arrow_diagram_func K C B X b)) (@one_cat_native_snake_kernel_first K C (@additive_preadditive
  C Prod t Add) C1 t (@additive_terminal_object C Prod t Add) T0 P Q A B X D b c h)
  (@one_cat_native_snake_six_term_result K C C1 Prod t Add T0 P Q N A B X D b c h)) (@finite_arrow_tail_arrow
  (Functor_cat K C) (@OneCatNativeExactArrowPair K C (@additive_preadditive C Prod t Add) C1 t
  (@additive_terminal_object C Prod t Add) T0 P Q N) (succ (succ (succ zero))) (@kernel_adjunction_family_func K
  C (@additive_preadditive C Prod t Add) t (@additive_terminal_object C Prod t Add) P
  (@one_cat_native_snake_alpha_diagram K C (@additive_preadditive C Prod t Add) C1 t (@additive_terminal_object
  C Prod t Add) T0 P A B X D b c h)) (@kernel_adjunction_family_func K C (@additive_preadditive C Prod t Add) t
  (@additive_terminal_object C Prod t Add) P (@transf_arrow_diagram_func K C B X b))
  (@one_cat_native_snake_kernel_first K C (@additive_preadditive C Prod t Add) C1 t (@additive_terminal_object C
  Prod t Add) T0 P Q A B X D b c h) (@one_cat_native_snake_six_term_result K C C1 Prod t Add T0 P Q N A B X D b
  c h)) (@finite_arrow_tail_rest (Functor_cat K C) (@OneCatNativeExactArrowPair K C (@additive_preadditive C
  Prod t Add) C1 t (@additive_terminal_object C Prod t Add) T0 P Q N) (succ (succ (succ zero)))
  (@kernel_adjunction_family_func K C (@additive_preadditive C Prod t Add) t (@additive_terminal_object C Prod t
  Add) P (@one_cat_native_snake_alpha_diagram K C (@additive_preadditive C Prod t Add) C1 t
  (@additive_terminal_object C Prod t Add) T0 P A B X D b c h)) (@kernel_adjunction_family_func K C
  (@additive_preadditive C Prod t Add) t (@additive_terminal_object C Prod t Add) P (@transf_arrow_diagram_func
  K C B X b)) (@one_cat_native_snake_kernel_first K C (@additive_preadditive C Prod t Add) C1 t
  (@additive_terminal_object C Prod t Add) T0 P Q A B X D b c h) (@one_cat_native_snake_six_term_result K C C1
  Prod t Add T0 P Q N A B X D b c h))) (@finite_arrow_tail_arrow (Functor_cat K C) (@OneCatNativeExactArrowPair
  K C (@additive_preadditive C Prod t Add) C1 t (@additive_terminal_object C Prod t Add) T0 P Q N) (succ (succ
  zero)) (@kernel_adjunction_family_func K C (@additive_preadditive C Prod t Add) t (@additive_terminal_object C
  Prod t Add) P (@transf_arrow_diagram_func K C B X b)) (@finite_arrow_tail_next (Functor_cat K C)
  (@OneCatNativeExactArrowPair K C (@additive_preadditive C Prod t Add) C1 t (@additive_terminal_object C Prod t
  Add) T0 P Q N) (succ (succ (succ zero))) (@kernel_adjunction_family_func K C (@additive_preadditive C Prod t
  Add) t (@additive_terminal_object C Prod t Add) P (@one_cat_native_snake_alpha_diagram K C
  (@additive_preadditive C Prod t Add) C1 t (@additive_terminal_object C Prod t Add) T0 P A B X D b c h))
  (@kernel_adjunction_family_func K C (@additive_preadditive C Prod t Add) t (@additive_terminal_object C Prod t
  Add) P (@transf_arrow_diagram_func K C B X b)) (@one_cat_native_snake_kernel_first K C (@additive_preadditive
  C Prod t Add) C1 t (@additive_terminal_object C Prod t Add) T0 P Q A B X D b c h)
  (@one_cat_native_snake_six_term_result K C C1 Prod t Add T0 P Q N A B X D b c h)) (@finite_arrow_tail_arrow
  (Functor_cat K C) (@OneCatNativeExactArrowPair K C (@additive_preadditive C Prod t Add) C1 t
  (@additive_terminal_object C Prod t Add) T0 P Q N) (succ (succ (succ zero))) (@kernel_adjunction_family_func K
  C (@additive_preadditive C Prod t Add) t (@additive_terminal_object C Prod t Add) P
  (@one_cat_native_snake_alpha_diagram K C (@additive_preadditive C Prod t Add) C1 t (@additive_terminal_object
  C Prod t Add) T0 P A B X D b c h)) (@kernel_adjunction_family_func K C (@additive_preadditive C Prod t Add) t
  (@additive_terminal_object C Prod t Add) P (@transf_arrow_diagram_func K C B X b))
  (@one_cat_native_snake_kernel_first K C (@additive_preadditive C Prod t Add) C1 t (@additive_terminal_object C
  Prod t Add) T0 P Q A B X D b c h) (@one_cat_native_snake_six_term_result K C C1 Prod t Add T0 P Q N A B X D b
  c h)) (@finite_arrow_tail_rest (Functor_cat K C) (@OneCatNativeExactArrowPair K C (@additive_preadditive C
  Prod t Add) C1 t (@additive_terminal_object C Prod t Add) T0 P Q N) (succ (succ (succ zero)))
  (@kernel_adjunction_family_func K C (@additive_preadditive C Prod t Add) t (@additive_terminal_object C Prod t
  Add) P (@one_cat_native_snake_alpha_diagram K C (@additive_preadditive C Prod t Add) C1 t
  (@additive_terminal_object C Prod t Add) T0 P A B X D b c h)) (@kernel_adjunction_family_func K C
  (@additive_preadditive C Prod t Add) t (@additive_terminal_object C Prod t Add) P (@transf_arrow_diagram_func
  K C B X b)) (@one_cat_native_snake_kernel_first K C (@additive_preadditive C Prod t Add) C1 t
  (@additive_terminal_object C Prod t Add) T0 P Q A B X D b c h) (@one_cat_native_snake_six_term_result K C C1
  Prod t Add T0 P Q N A B X D b c h))) (@finite_arrow_tail_rest (Functor_cat K C) (@OneCatNativeExactArrowPair K
  C (@additive_preadditive C Prod t Add) C1 t (@additive_terminal_object C Prod t Add) T0 P Q N) (succ (succ
  zero)) (@kernel_adjunction_family_func K C (@additive_preadditive C Prod t Add) t (@additive_terminal_object C
  Prod t Add) P (@transf_arrow_diagram_func K C B X b)) (@finite_arrow_tail_next (Functor_cat K C)
  (@OneCatNativeExactArrowPair K C (@additive_preadditive C Prod t Add) C1 t (@additive_terminal_object C Prod t
  Add) T0 P Q N) (succ (succ (succ zero))) (@kernel_adjunction_family_func K C (@additive_preadditive C Prod t
  Add) t (@additive_terminal_object C Prod t Add) P (@one_cat_native_snake_alpha_diagram K C
  (@additive_preadditive C Prod t Add) C1 t (@additive_terminal_object C Prod t Add) T0 P A B X D b c h))
  (@kernel_adjunction_family_func K C (@additive_preadditive C Prod t Add) t (@additive_terminal_object C Prod t
  Add) P (@transf_arrow_diagram_func K C B X b)) (@one_cat_native_snake_kernel_first K C (@additive_preadditive
  C Prod t Add) C1 t (@additive_terminal_object C Prod t Add) T0 P Q A B X D b c h)
  (@one_cat_native_snake_six_term_result K C C1 Prod t Add T0 P Q N A B X D b c h)) (@finite_arrow_tail_arrow
  (Functor_cat K C) (@OneCatNativeExactArrowPair K C (@additive_preadditive C Prod t Add) C1 t
  (@additive_terminal_object C Prod t Add) T0 P Q N) (succ (succ (succ zero))) (@kernel_adjunction_family_func K
  C (@additive_preadditive C Prod t Add) t (@additive_terminal_object C Prod t Add) P
  (@one_cat_native_snake_alpha_diagram K C (@additive_preadditive C Prod t Add) C1 t (@additive_terminal_object
  C Prod t Add) T0 P A B X D b c h)) (@kernel_adjunction_family_func K C (@additive_preadditive C Prod t Add) t
  (@additive_terminal_object C Prod t Add) P (@transf_arrow_diagram_func K C B X b))
  (@one_cat_native_snake_kernel_first K C (@additive_preadditive C Prod t Add) C1 t (@additive_terminal_object C
  Prod t Add) T0 P Q A B X D b c h) (@one_cat_native_snake_six_term_result K C C1 Prod t Add T0 P Q N A B X D b
  c h)) (@finite_arrow_tail_rest (Functor_cat K C) (@OneCatNativeExactArrowPair K C (@additive_preadditive C
  Prod t Add) C1 t (@additive_terminal_object C Prod t Add) T0 P Q N) (succ (succ (succ zero)))
  (@kernel_adjunction_family_func K C (@additive_preadditive C Prod t Add) t (@additive_terminal_object C Prod t
  Add) P (@one_cat_native_snake_alpha_diagram K C (@additive_preadditive C Prod t Add) C1 t
  (@additive_terminal_object C Prod t Add) T0 P A B X D b c h)) (@kernel_adjunction_family_func K C
  (@additive_preadditive C Prod t Add) t (@additive_terminal_object C Prod t Add) P (@transf_arrow_diagram_func
  K C B X b)) (@one_cat_native_snake_kernel_first K C (@additive_preadditive C Prod t Add) C1 t
  (@additive_terminal_object C Prod t Add) T0 P Q A B X D b c h) (@one_cat_native_snake_six_term_result K C C1
  Prod t Add T0 P Q N A B X D b c h)))) (@finite_arrow_tail_arrow (Functor_cat K C) (@OneCatNativeExactArrowPair
  K C (@additive_preadditive C Prod t Add) C1 t (@additive_terminal_object C Prod t Add) T0 P Q N) (succ zero)
  (@finite_arrow_tail_next (Functor_cat K C) (@OneCatNativeExactArrowPair K C (@additive_preadditive C Prod t
  Add) C1 t (@additive_terminal_object C Prod t Add) T0 P Q N) (succ (succ (succ zero)))
  (@kernel_adjunction_family_func K C (@additive_preadditive C Prod t Add) t (@additive_terminal_object C Prod t
  Add) P (@one_cat_native_snake_alpha_diagram K C (@additive_preadditive C Prod t Add) C1 t
  (@additive_terminal_object C Prod t Add) T0 P A B X D b c h)) (@kernel_adjunction_family_func K C
  (@additive_preadditive C Prod t Add) t (@additive_terminal_object C Prod t Add) P (@transf_arrow_diagram_func
  K C B X b)) (@one_cat_native_snake_kernel_first K C (@additive_preadditive C Prod t Add) C1 t
  (@additive_terminal_object C Prod t Add) T0 P Q A B X D b c h) (@one_cat_native_snake_six_term_result K C C1
  Prod t Add T0 P Q N A B X D b c h)) (@finite_arrow_tail_next (Functor_cat K C) (@OneCatNativeExactArrowPair K
  C (@additive_preadditive C Prod t Add) C1 t (@additive_terminal_object C Prod t Add) T0 P Q N) (succ (succ
  zero)) (@kernel_adjunction_family_func K C (@additive_preadditive C Prod t Add) t (@additive_terminal_object C
  Prod t Add) P (@transf_arrow_diagram_func K C B X b)) (@finite_arrow_tail_next (Functor_cat K C)
  (@OneCatNativeExactArrowPair K C (@additive_preadditive C Prod t Add) C1 t (@additive_terminal_object C Prod t
  Add) T0 P Q N) (succ (succ (succ zero))) (@kernel_adjunction_family_func K C (@additive_preadditive C Prod t
  Add) t (@additive_terminal_object C Prod t Add) P (@one_cat_native_snake_alpha_diagram K C
  (@additive_preadditive C Prod t Add) C1 t (@additive_terminal_object C Prod t Add) T0 P A B X D b c h))
  (@kernel_adjunction_family_func K C (@additive_preadditive C Prod t Add) t (@additive_terminal_object C Prod t
  Add) P (@transf_arrow_diagram_func K C B X b)) (@one_cat_native_snake_kernel_first K C (@additive_preadditive
  C Prod t Add) C1 t (@additive_terminal_object C Prod t Add) T0 P Q A B X D b c h)
  (@one_cat_native_snake_six_term_result K C C1 Prod t Add T0 P Q N A B X D b c h)) (@finite_arrow_tail_arrow
  (Functor_cat K C) (@OneCatNativeExactArrowPair K C (@additive_preadditive C Prod t Add) C1 t
  (@additive_terminal_object C Prod t Add) T0 P Q N) (succ (succ (succ zero))) (@kernel_adjunction_family_func K
  C (@additive_preadditive C Prod t Add) t (@additive_terminal_object C Prod t Add) P
  (@one_cat_native_snake_alpha_diagram K C (@additive_preadditive C Prod t Add) C1 t (@additive_terminal_object
  C Prod t Add) T0 P A B X D b c h)) (@kernel_adjunction_family_func K C (@additive_preadditive C Prod t Add) t
  (@additive_terminal_object C Prod t Add) P (@transf_arrow_diagram_func K C B X b))
  (@one_cat_native_snake_kernel_first K C (@additive_preadditive C Prod t Add) C1 t (@additive_terminal_object C
  Prod t Add) T0 P Q A B X D b c h) (@one_cat_native_snake_six_term_result K C C1 Prod t Add T0 P Q N A B X D b
  c h)) (@finite_arrow_tail_rest (Functor_cat K C) (@OneCatNativeExactArrowPair K C (@additive_preadditive C
  Prod t Add) C1 t (@additive_terminal_object C Prod t Add) T0 P Q N) (succ (succ (succ zero)))
  (@kernel_adjunction_family_func K C (@additive_preadditive C Prod t Add) t (@additive_terminal_object C Prod t
  Add) P (@one_cat_native_snake_alpha_diagram K C (@additive_preadditive C Prod t Add) C1 t
  (@additive_terminal_object C Prod t Add) T0 P A B X D b c h)) (@kernel_adjunction_family_func K C
  (@additive_preadditive C Prod t Add) t (@additive_terminal_object C Prod t Add) P (@transf_arrow_diagram_func
  K C B X b)) (@one_cat_native_snake_kernel_first K C (@additive_preadditive C Prod t Add) C1 t
  (@additive_terminal_object C Prod t Add) T0 P Q A B X D b c h) (@one_cat_native_snake_six_term_result K C C1
  Prod t Add T0 P Q N A B X D b c h))) (@finite_arrow_tail_arrow (Functor_cat K C) (@OneCatNativeExactArrowPair
  K C (@additive_preadditive C Prod t Add) C1 t (@additive_terminal_object C Prod t Add) T0 P Q N) (succ (succ
  zero)) (@kernel_adjunction_family_func K C (@additive_preadditive C Prod t Add) t (@additive_terminal_object C
  Prod t Add) P (@transf_arrow_diagram_func K C B X b)) (@finite_arrow_tail_next (Functor_cat K C)
  (@OneCatNativeExactArrowPair K C (@additive_preadditive C Prod t Add) C1 t (@additive_terminal_object C Prod t
  Add) T0 P Q N) (succ (succ (succ zero))) (@kernel_adjunction_family_func K C (@additive_preadditive C Prod t
  Add) t (@additive_terminal_object C Prod t Add) P (@one_cat_native_snake_alpha_diagram K C
  (@additive_preadditive C Prod t Add) C1 t (@additive_terminal_object C Prod t Add) T0 P A B X D b c h))
  (@kernel_adjunction_family_func K C (@additive_preadditive C Prod t Add) t (@additive_terminal_object C Prod t
  Add) P (@transf_arrow_diagram_func K C B X b)) (@one_cat_native_snake_kernel_first K C (@additive_preadditive
  C Prod t Add) C1 t (@additive_terminal_object C Prod t Add) T0 P Q A B X D b c h)
  (@one_cat_native_snake_six_term_result K C C1 Prod t Add T0 P Q N A B X D b c h)) (@finite_arrow_tail_arrow
  (Functor_cat K C) (@OneCatNativeExactArrowPair K C (@additive_preadditive C Prod t Add) C1 t
  (@additive_terminal_object C Prod t Add) T0 P Q N) (succ (succ (succ zero))) (@kernel_adjunction_family_func K
  C (@additive_preadditive C Prod t Add) t (@additive_terminal_object C Prod t Add) P
  (@one_cat_native_snake_alpha_diagram K C (@additive_preadditive C Prod t Add) C1 t (@additive_terminal_object
  C Prod t Add) T0 P A B X D b c h)) (@kernel_adjunction_family_func K C (@additive_preadditive C Prod t Add) t
  (@additive_terminal_object C Prod t Add) P (@transf_arrow_diagram_func K C B X b))
  (@one_cat_native_snake_kernel_first K C (@additive_preadditive C Prod t Add) C1 t (@additive_terminal_object C
  Prod t Add) T0 P Q A B X D b c h) (@one_cat_native_snake_six_term_result K C C1 Prod t Add T0 P Q N A B X D b
  c h)) (@finite_arrow_tail_rest (Functor_cat K C) (@OneCatNativeExactArrowPair K C (@additive_preadditive C
  Prod t Add) C1 t (@additive_terminal_object C Prod t Add) T0 P Q N) (succ (succ (succ zero)))
  (@kernel_adjunction_family_func K C (@additive_preadditive C Prod t Add) t (@additive_terminal_object C Prod t
  Add) P (@one_cat_native_snake_alpha_diagram K C (@additive_preadditive C Prod t Add) C1 t
  (@additive_terminal_object C Prod t Add) T0 P A B X D b c h)) (@kernel_adjunction_family_func K C
  (@additive_preadditive C Prod t Add) t (@additive_terminal_object C Prod t Add) P (@transf_arrow_diagram_func
  K C B X b)) (@one_cat_native_snake_kernel_first K C (@additive_preadditive C Prod t Add) C1 t
  (@additive_terminal_object C Prod t Add) T0 P Q A B X D b c h) (@one_cat_native_snake_six_term_result K C C1
  Prod t Add T0 P Q N A B X D b c h))) (@finite_arrow_tail_rest (Functor_cat K C) (@OneCatNativeExactArrowPair K
  C (@additive_preadditive C Prod t Add) C1 t (@additive_terminal_object C Prod t Add) T0 P Q N) (succ (succ
  zero)) (@kernel_adjunction_family_func K C (@additive_preadditive C Prod t Add) t (@additive_terminal_object C
  Prod t Add) P (@transf_arrow_diagram_func K C B X b)) (@finite_arrow_tail_next (Functor_cat K C)
  (@OneCatNativeExactArrowPair K C (@additive_preadditive C Prod t Add) C1 t (@additive_terminal_object C Prod t
  Add) T0 P Q N) (succ (succ (succ zero))) (@kernel_adjunction_family_func K C (@additive_preadditive C Prod t
  Add) t (@additive_terminal_object C Prod t Add) P (@one_cat_native_snake_alpha_diagram K C
  (@additive_preadditive C Prod t Add) C1 t (@additive_terminal_object C Prod t Add) T0 P A B X D b c h))
  (@kernel_adjunction_family_func K C (@additive_preadditive C Prod t Add) t (@additive_terminal_object C Prod t
  Add) P (@transf_arrow_diagram_func K C B X b)) (@one_cat_native_snake_kernel_first K C (@additive_preadditive
  C Prod t Add) C1 t (@additive_terminal_object C Prod t Add) T0 P Q A B X D b c h)
  (@one_cat_native_snake_six_term_result K C C1 Prod t Add T0 P Q N A B X D b c h)) (@finite_arrow_tail_arrow
  (Functor_cat K C) (@OneCatNativeExactArrowPair K C (@additive_preadditive C Prod t Add) C1 t
  (@additive_terminal_object C Prod t Add) T0 P Q N) (succ (succ (succ zero))) (@kernel_adjunction_family_func K
  C (@additive_preadditive C Prod t Add) t (@additive_terminal_object C Prod t Add) P
  (@one_cat_native_snake_alpha_diagram K C (@additive_preadditive C Prod t Add) C1 t (@additive_terminal_object
  C Prod t Add) T0 P A B X D b c h)) (@kernel_adjunction_family_func K C (@additive_preadditive C Prod t Add) t
  (@additive_terminal_object C Prod t Add) P (@transf_arrow_diagram_func K C B X b))
  (@one_cat_native_snake_kernel_first K C (@additive_preadditive C Prod t Add) C1 t (@additive_terminal_object C
  Prod t Add) T0 P Q A B X D b c h) (@one_cat_native_snake_six_term_result K C C1 Prod t Add T0 P Q N A B X D b
  c h)) (@finite_arrow_tail_rest (Functor_cat K C) (@OneCatNativeExactArrowPair K C (@additive_preadditive C
  Prod t Add) C1 t (@additive_terminal_object C Prod t Add) T0 P Q N) (succ (succ (succ zero)))
  (@kernel_adjunction_family_func K C (@additive_preadditive C Prod t Add) t (@additive_terminal_object C Prod t
  Add) P (@one_cat_native_snake_alpha_diagram K C (@additive_preadditive C Prod t Add) C1 t
  (@additive_terminal_object C Prod t Add) T0 P A B X D b c h)) (@kernel_adjunction_family_func K C
  (@additive_preadditive C Prod t Add) t (@additive_terminal_object C Prod t Add) P (@transf_arrow_diagram_func
  K C B X b)) (@one_cat_native_snake_kernel_first K C (@additive_preadditive C Prod t Add) C1 t
  (@additive_terminal_object C Prod t Add) T0 P Q A B X D b c h) (@one_cat_native_snake_six_term_result K C C1
  Prod t Add T0 P Q N A B X D b c h)))) (@finite_arrow_tail_rest (Functor_cat K C) (@OneCatNativeExactArrowPair
  K C (@additive_preadditive C Prod t Add) C1 t (@additive_terminal_object C Prod t Add) T0 P Q N) (succ zero)
  (@finite_arrow_tail_next (Functor_cat K C) (@OneCatNativeExactArrowPair K C (@additive_preadditive C Prod t
  Add) C1 t (@additive_terminal_object C Prod t Add) T0 P Q N) (succ (succ (succ zero)))
  (@kernel_adjunction_family_func K C (@additive_preadditive C Prod t Add) t (@additive_terminal_object C Prod t
  Add) P (@one_cat_native_snake_alpha_diagram K C (@additive_preadditive C Prod t Add) C1 t
  (@additive_terminal_object C Prod t Add) T0 P A B X D b c h)) (@kernel_adjunction_family_func K C
  (@additive_preadditive C Prod t Add) t (@additive_terminal_object C Prod t Add) P (@transf_arrow_diagram_func
  K C B X b)) (@one_cat_native_snake_kernel_first K C (@additive_preadditive C Prod t Add) C1 t
  (@additive_terminal_object C Prod t Add) T0 P Q A B X D b c h) (@one_cat_native_snake_six_term_result K C C1
  Prod t Add T0 P Q N A B X D b c h)) (@finite_arrow_tail_next (Functor_cat K C) (@OneCatNativeExactArrowPair K
  C (@additive_preadditive C Prod t Add) C1 t (@additive_terminal_object C Prod t Add) T0 P Q N) (succ (succ
  zero)) (@kernel_adjunction_family_func K C (@additive_preadditive C Prod t Add) t (@additive_terminal_object C
  Prod t Add) P (@transf_arrow_diagram_func K C B X b)) (@finite_arrow_tail_next (Functor_cat K C)
  (@OneCatNativeExactArrowPair K C (@additive_preadditive C Prod t Add) C1 t (@additive_terminal_object C Prod t
  Add) T0 P Q N) (succ (succ (succ zero))) (@kernel_adjunction_family_func K C (@additive_preadditive C Prod t
  Add) t (@additive_terminal_object C Prod t Add) P (@one_cat_native_snake_alpha_diagram K C
  (@additive_preadditive C Prod t Add) C1 t (@additive_terminal_object C Prod t Add) T0 P A B X D b c h))
  (@kernel_adjunction_family_func K C (@additive_preadditive C Prod t Add) t (@additive_terminal_object C Prod t
  Add) P (@transf_arrow_diagram_func K C B X b)) (@one_cat_native_snake_kernel_first K C (@additive_preadditive
  C Prod t Add) C1 t (@additive_terminal_object C Prod t Add) T0 P Q A B X D b c h)
  (@one_cat_native_snake_six_term_result K C C1 Prod t Add T0 P Q N A B X D b c h)) (@finite_arrow_tail_arrow
  (Functor_cat K C) (@OneCatNativeExactArrowPair K C (@additive_preadditive C Prod t Add) C1 t
  (@additive_terminal_object C Prod t Add) T0 P Q N) (succ (succ (succ zero))) (@kernel_adjunction_family_func K
  C (@additive_preadditive C Prod t Add) t (@additive_terminal_object C Prod t Add) P
  (@one_cat_native_snake_alpha_diagram K C (@additive_preadditive C Prod t Add) C1 t (@additive_terminal_object
  C Prod t Add) T0 P A B X D b c h)) (@kernel_adjunction_family_func K C (@additive_preadditive C Prod t Add) t
  (@additive_terminal_object C Prod t Add) P (@transf_arrow_diagram_func K C B X b))
  (@one_cat_native_snake_kernel_first K C (@additive_preadditive C Prod t Add) C1 t (@additive_terminal_object C
  Prod t Add) T0 P Q A B X D b c h) (@one_cat_native_snake_six_term_result K C C1 Prod t Add T0 P Q N A B X D b
  c h)) (@finite_arrow_tail_rest (Functor_cat K C) (@OneCatNativeExactArrowPair K C (@additive_preadditive C
  Prod t Add) C1 t (@additive_terminal_object C Prod t Add) T0 P Q N) (succ (succ (succ zero)))
  (@kernel_adjunction_family_func K C (@additive_preadditive C Prod t Add) t (@additive_terminal_object C Prod t
  Add) P (@one_cat_native_snake_alpha_diagram K C (@additive_preadditive C Prod t Add) C1 t
  (@additive_terminal_object C Prod t Add) T0 P A B X D b c h)) (@kernel_adjunction_family_func K C
  (@additive_preadditive C Prod t Add) t (@additive_terminal_object C Prod t Add) P (@transf_arrow_diagram_func
  K C B X b)) (@one_cat_native_snake_kernel_first K C (@additive_preadditive C Prod t Add) C1 t
  (@additive_terminal_object C Prod t Add) T0 P Q A B X D b c h) (@one_cat_native_snake_six_term_result K C C1
  Prod t Add T0 P Q N A B X D b c h))) (@finite_arrow_tail_arrow (Functor_cat K C) (@OneCatNativeExactArrowPair
  K C (@additive_preadditive C Prod t Add) C1 t (@additive_terminal_object C Prod t Add) T0 P Q N) (succ (succ
  zero)) (@kernel_adjunction_family_func K C (@additive_preadditive C Prod t Add) t (@additive_terminal_object C
  Prod t Add) P (@transf_arrow_diagram_func K C B X b)) (@finite_arrow_tail_next (Functor_cat K C)
  (@OneCatNativeExactArrowPair K C (@additive_preadditive C Prod t Add) C1 t (@additive_terminal_object C Prod t
  Add) T0 P Q N) (succ (succ (succ zero))) (@kernel_adjunction_family_func K C (@additive_preadditive C Prod t
  Add) t (@additive_terminal_object C Prod t Add) P (@one_cat_native_snake_alpha_diagram K C
  (@additive_preadditive C Prod t Add) C1 t (@additive_terminal_object C Prod t Add) T0 P A B X D b c h))
  (@kernel_adjunction_family_func K C (@additive_preadditive C Prod t Add) t (@additive_terminal_object C Prod t
  Add) P (@transf_arrow_diagram_func K C B X b)) (@one_cat_native_snake_kernel_first K C (@additive_preadditive
  C Prod t Add) C1 t (@additive_terminal_object C Prod t Add) T0 P Q A B X D b c h)
  (@one_cat_native_snake_six_term_result K C C1 Prod t Add T0 P Q N A B X D b c h)) (@finite_arrow_tail_arrow
  (Functor_cat K C) (@OneCatNativeExactArrowPair K C (@additive_preadditive C Prod t Add) C1 t
  (@additive_terminal_object C Prod t Add) T0 P Q N) (succ (succ (succ zero))) (@kernel_adjunction_family_func K
  C (@additive_preadditive C Prod t Add) t (@additive_terminal_object C Prod t Add) P
  (@one_cat_native_snake_alpha_diagram K C (@additive_preadditive C Prod t Add) C1 t (@additive_terminal_object
  C Prod t Add) T0 P A B X D b c h)) (@kernel_adjunction_family_func K C (@additive_preadditive C Prod t Add) t
  (@additive_terminal_object C Prod t Add) P (@transf_arrow_diagram_func K C B X b))
  (@one_cat_native_snake_kernel_first K C (@additive_preadditive C Prod t Add) C1 t (@additive_terminal_object C
  Prod t Add) T0 P Q A B X D b c h) (@one_cat_native_snake_six_term_result K C C1 Prod t Add T0 P Q N A B X D b
  c h)) (@finite_arrow_tail_rest (Functor_cat K C) (@OneCatNativeExactArrowPair K C (@additive_preadditive C
  Prod t Add) C1 t (@additive_terminal_object C Prod t Add) T0 P Q N) (succ (succ (succ zero)))
  (@kernel_adjunction_family_func K C (@additive_preadditive C Prod t Add) t (@additive_terminal_object C Prod t
  Add) P (@one_cat_native_snake_alpha_diagram K C (@additive_preadditive C Prod t Add) C1 t
  (@additive_terminal_object C Prod t Add) T0 P A B X D b c h)) (@kernel_adjunction_family_func K C
  (@additive_preadditive C Prod t Add) t (@additive_terminal_object C Prod t Add) P (@transf_arrow_diagram_func
  K C B X b)) (@one_cat_native_snake_kernel_first K C (@additive_preadditive C Prod t Add) C1 t
  (@additive_terminal_object C Prod t Add) T0 P Q A B X D b c h) (@one_cat_native_snake_six_term_result K C C1
  Prod t Add T0 P Q N A B X D b c h))) (@finite_arrow_tail_rest (Functor_cat K C) (@OneCatNativeExactArrowPair K
  C (@additive_preadditive C Prod t Add) C1 t (@additive_terminal_object C Prod t Add) T0 P Q N) (succ (succ
  zero)) (@kernel_adjunction_family_func K C (@additive_preadditive C Prod t Add) t (@additive_terminal_object C
  Prod t Add) P (@transf_arrow_diagram_func K C B X b)) (@finite_arrow_tail_next (Functor_cat K C)
  (@OneCatNativeExactArrowPair K C (@additive_preadditive C Prod t Add) C1 t (@additive_terminal_object C Prod t
  Add) T0 P Q N) (succ (succ (succ zero))) (@kernel_adjunction_family_func K C (@additive_preadditive C Prod t
  Add) t (@additive_terminal_object C Prod t Add) P (@one_cat_native_snake_alpha_diagram K C
  (@additive_preadditive C Prod t Add) C1 t (@additive_terminal_object C Prod t Add) T0 P A B X D b c h))
  (@kernel_adjunction_family_func K C (@additive_preadditive C Prod t Add) t (@additive_terminal_object C Prod t
  Add) P (@transf_arrow_diagram_func K C B X b)) (@one_cat_native_snake_kernel_first K C (@additive_preadditive
  C Prod t Add) C1 t (@additive_terminal_object C Prod t Add) T0 P Q A B X D b c h)
  (@one_cat_native_snake_six_term_result K C C1 Prod t Add T0 P Q N A B X D b c h)) (@finite_arrow_tail_arrow
  (Functor_cat K C) (@OneCatNativeExactArrowPair K C (@additive_preadditive C Prod t Add) C1 t
  (@additive_terminal_object C Prod t Add) T0 P Q N) (succ (succ (succ zero))) (@kernel_adjunction_family_func K
  C (@additive_preadditive C Prod t Add) t (@additive_terminal_object C Prod t Add) P
  (@one_cat_native_snake_alpha_diagram K C (@additive_preadditive C Prod t Add) C1 t (@additive_terminal_object
  C Prod t Add) T0 P A B X D b c h)) (@kernel_adjunction_family_func K C (@additive_preadditive C Prod t Add) t
  (@additive_terminal_object C Prod t Add) P (@transf_arrow_diagram_func K C B X b))
  (@one_cat_native_snake_kernel_first K C (@additive_preadditive C Prod t Add) C1 t (@additive_terminal_object C
  Prod t Add) T0 P Q A B X D b c h) (@one_cat_native_snake_six_term_result K C C1 Prod t Add T0 P Q N A B X D b
  c h)) (@finite_arrow_tail_rest (Functor_cat K C) (@OneCatNativeExactArrowPair K C (@additive_preadditive C
  Prod t Add) C1 t (@additive_terminal_object C Prod t Add) T0 P Q N) (succ (succ (succ zero)))
  (@kernel_adjunction_family_func K C (@additive_preadditive C Prod t Add) t (@additive_terminal_object C Prod t
  Add) P (@one_cat_native_snake_alpha_diagram K C (@additive_preadditive C Prod t Add) C1 t
  (@additive_terminal_object C Prod t Add) T0 P A B X D b c h)) (@kernel_adjunction_family_func K C
  (@additive_preadditive C Prod t Add) t (@additive_terminal_object C Prod t Add) P (@transf_arrow_diagram_func
  K C B X b)) (@one_cat_native_snake_kernel_first K C (@additive_preadditive C Prod t Add) C1 t
  (@additive_terminal_object C Prod t Add) T0 P Q A B X D b c h) (@one_cat_native_snake_six_term_result K C C1
  Prod t Add T0 P Q N A B X D b c h)))))) (@comp_fapp0 (Functor_cat K C) (@finite_arrow_tail_next (Functor_cat K
  C) (@OneCatNativeExactArrowPair K C (@additive_preadditive C Prod t Add) C1 t (@additive_terminal_object C
  Prod t Add) T0 P Q N) (succ (succ zero)) (@kernel_adjunction_family_func K C (@additive_preadditive C Prod t
  Add) t (@additive_terminal_object C Prod t Add) P (@transf_arrow_diagram_func K C B X b))
  (@finite_arrow_tail_next (Functor_cat K C) (@OneCatNativeExactArrowPair K C (@additive_preadditive C Prod t
  Add) C1 t (@additive_terminal_object C Prod t Add) T0 P Q N) (succ (succ (succ zero)))
  (@kernel_adjunction_family_func K C (@additive_preadditive C Prod t Add) t (@additive_terminal_object C Prod t
  Add) P (@one_cat_native_snake_alpha_diagram K C (@additive_preadditive C Prod t Add) C1 t
  (@additive_terminal_object C Prod t Add) T0 P A B X D b c h)) (@kernel_adjunction_family_func K C
  (@additive_preadditive C Prod t Add) t (@additive_terminal_object C Prod t Add) P (@transf_arrow_diagram_func
  K C B X b)) (@one_cat_native_snake_kernel_first K C (@additive_preadditive C Prod t Add) C1 t
  (@additive_terminal_object C Prod t Add) T0 P Q A B X D b c h) (@one_cat_native_snake_six_term_result K C C1
  Prod t Add T0 P Q N A B X D b c h)) (@finite_arrow_tail_arrow (Functor_cat K C) (@OneCatNativeExactArrowPair K
  C (@additive_preadditive C Prod t Add) C1 t (@additive_terminal_object C Prod t Add) T0 P Q N) (succ (succ
  (succ zero))) (@kernel_adjunction_family_func K C (@additive_preadditive C Prod t Add) t
  (@additive_terminal_object C Prod t Add) P (@one_cat_native_snake_alpha_diagram K C (@additive_preadditive C
  Prod t Add) C1 t (@additive_terminal_object C Prod t Add) T0 P A B X D b c h)) (@kernel_adjunction_family_func
  K C (@additive_preadditive C Prod t Add) t (@additive_terminal_object C Prod t Add) P
  (@transf_arrow_diagram_func K C B X b)) (@one_cat_native_snake_kernel_first K C (@additive_preadditive C Prod
  t Add) C1 t (@additive_terminal_object C Prod t Add) T0 P Q A B X D b c h)
  (@one_cat_native_snake_six_term_result K C C1 Prod t Add T0 P Q N A B X D b c h)) (@finite_arrow_tail_rest
  (Functor_cat K C) (@OneCatNativeExactArrowPair K C (@additive_preadditive C Prod t Add) C1 t
  (@additive_terminal_object C Prod t Add) T0 P Q N) (succ (succ (succ zero))) (@kernel_adjunction_family_func K
  C (@additive_preadditive C Prod t Add) t (@additive_terminal_object C Prod t Add) P
  (@one_cat_native_snake_alpha_diagram K C (@additive_preadditive C Prod t Add) C1 t (@additive_terminal_object
  C Prod t Add) T0 P A B X D b c h)) (@kernel_adjunction_family_func K C (@additive_preadditive C Prod t Add) t
  (@additive_terminal_object C Prod t Add) P (@transf_arrow_diagram_func K C B X b))
  (@one_cat_native_snake_kernel_first K C (@additive_preadditive C Prod t Add) C1 t (@additive_terminal_object C
  Prod t Add) T0 P Q A B X D b c h) (@one_cat_native_snake_six_term_result K C C1 Prod t Add T0 P Q N A B X D b
  c h))) (@finite_arrow_tail_next (Functor_cat K C) (@OneCatNativeExactArrowPair K C (@additive_preadditive C
  Prod t Add) C1 t (@additive_terminal_object C Prod t Add) T0 P Q N) (succ zero) (@finite_arrow_tail_next
  (Functor_cat K C) (@OneCatNativeExactArrowPair K C (@additive_preadditive C Prod t Add) C1 t
  (@additive_terminal_object C Prod t Add) T0 P Q N) (succ (succ (succ zero))) (@kernel_adjunction_family_func K
  C (@additive_preadditive C Prod t Add) t (@additive_terminal_object C Prod t Add) P
  (@one_cat_native_snake_alpha_diagram K C (@additive_preadditive C Prod t Add) C1 t (@additive_terminal_object
  C Prod t Add) T0 P A B X D b c h)) (@kernel_adjunction_family_func K C (@additive_preadditive C Prod t Add) t
  (@additive_terminal_object C Prod t Add) P (@transf_arrow_diagram_func K C B X b))
  (@one_cat_native_snake_kernel_first K C (@additive_preadditive C Prod t Add) C1 t (@additive_terminal_object C
  Prod t Add) T0 P Q A B X D b c h) (@one_cat_native_snake_six_term_result K C C1 Prod t Add T0 P Q N A B X D b
  c h)) (@finite_arrow_tail_next (Functor_cat K C) (@OneCatNativeExactArrowPair K C (@additive_preadditive C
  Prod t Add) C1 t (@additive_terminal_object C Prod t Add) T0 P Q N) (succ (succ zero))
  (@kernel_adjunction_family_func K C (@additive_preadditive C Prod t Add) t (@additive_terminal_object C Prod t
  Add) P (@transf_arrow_diagram_func K C B X b)) (@finite_arrow_tail_next (Functor_cat K C)
  (@OneCatNativeExactArrowPair K C (@additive_preadditive C Prod t Add) C1 t (@additive_terminal_object C Prod t
  Add) T0 P Q N) (succ (succ (succ zero))) (@kernel_adjunction_family_func K C (@additive_preadditive C Prod t
  Add) t (@additive_terminal_object C Prod t Add) P (@one_cat_native_snake_alpha_diagram K C
  (@additive_preadditive C Prod t Add) C1 t (@additive_terminal_object C Prod t Add) T0 P A B X D b c h))
  (@kernel_adjunction_family_func K C (@additive_preadditive C Prod t Add) t (@additive_terminal_object C Prod t
  Add) P (@transf_arrow_diagram_func K C B X b)) (@one_cat_native_snake_kernel_first K C (@additive_preadditive
  C Prod t Add) C1 t (@additive_terminal_object C Prod t Add) T0 P Q A B X D b c h)
  (@one_cat_native_snake_six_term_result K C C1 Prod t Add T0 P Q N A B X D b c h)) (@finite_arrow_tail_arrow
  (Functor_cat K C) (@OneCatNativeExactArrowPair K C (@additive_preadditive C Prod t Add) C1 t
  (@additive_terminal_object C Prod t Add) T0 P Q N) (succ (succ (succ zero))) (@kernel_adjunction_family_func K
  C (@additive_preadditive C Prod t Add) t (@additive_terminal_object C Prod t Add) P
  (@one_cat_native_snake_alpha_diagram K C (@additive_preadditive C Prod t Add) C1 t (@additive_terminal_object
  C Prod t Add) T0 P A B X D b c h)) (@kernel_adjunction_family_func K C (@additive_preadditive C Prod t Add) t
  (@additive_terminal_object C Prod t Add) P (@transf_arrow_diagram_func K C B X b))
  (@one_cat_native_snake_kernel_first K C (@additive_preadditive C Prod t Add) C1 t (@additive_terminal_object C
  Prod t Add) T0 P Q A B X D b c h) (@one_cat_native_snake_six_term_result K C C1 Prod t Add T0 P Q N A B X D b
  c h)) (@finite_arrow_tail_rest (Functor_cat K C) (@OneCatNativeExactArrowPair K C (@additive_preadditive C
  Prod t Add) C1 t (@additive_terminal_object C Prod t Add) T0 P Q N) (succ (succ (succ zero)))
  (@kernel_adjunction_family_func K C (@additive_preadditive C Prod t Add) t (@additive_terminal_object C Prod t
  Add) P (@one_cat_native_snake_alpha_diagram K C (@additive_preadditive C Prod t Add) C1 t
  (@additive_terminal_object C Prod t Add) T0 P A B X D b c h)) (@kernel_adjunction_family_func K C
  (@additive_preadditive C Prod t Add) t (@additive_terminal_object C Prod t Add) P (@transf_arrow_diagram_func
  K C B X b)) (@one_cat_native_snake_kernel_first K C (@additive_preadditive C Prod t Add) C1 t
  (@additive_terminal_object C Prod t Add) T0 P Q A B X D b c h) (@one_cat_native_snake_six_term_result K C C1
  Prod t Add T0 P Q N A B X D b c h))) (@finite_arrow_tail_arrow (Functor_cat K C) (@OneCatNativeExactArrowPair
  K C (@additive_preadditive C Prod t Add) C1 t (@additive_terminal_object C Prod t Add) T0 P Q N) (succ (succ
  zero)) (@kernel_adjunction_family_func K C (@additive_preadditive C Prod t Add) t (@additive_terminal_object C
  Prod t Add) P (@transf_arrow_diagram_func K C B X b)) (@finite_arrow_tail_next (Functor_cat K C)
  (@OneCatNativeExactArrowPair K C (@additive_preadditive C Prod t Add) C1 t (@additive_terminal_object C Prod t
  Add) T0 P Q N) (succ (succ (succ zero))) (@kernel_adjunction_family_func K C (@additive_preadditive C Prod t
  Add) t (@additive_terminal_object C Prod t Add) P (@one_cat_native_snake_alpha_diagram K C
  (@additive_preadditive C Prod t Add) C1 t (@additive_terminal_object C Prod t Add) T0 P A B X D b c h))
  (@kernel_adjunction_family_func K C (@additive_preadditive C Prod t Add) t (@additive_terminal_object C Prod t
  Add) P (@transf_arrow_diagram_func K C B X b)) (@one_cat_native_snake_kernel_first K C (@additive_preadditive
  C Prod t Add) C1 t (@additive_terminal_object C Prod t Add) T0 P Q A B X D b c h)
  (@one_cat_native_snake_six_term_result K C C1 Prod t Add T0 P Q N A B X D b c h)) (@finite_arrow_tail_arrow
  (Functor_cat K C) (@OneCatNativeExactArrowPair K C (@additive_preadditive C Prod t Add) C1 t
  (@additive_terminal_object C Prod t Add) T0 P Q N) (succ (succ (succ zero))) (@kernel_adjunction_family_func K
  C (@additive_preadditive C Prod t Add) t (@additive_terminal_object C Prod t Add) P
  (@one_cat_native_snake_alpha_diagram K C (@additive_preadditive C Prod t Add) C1 t (@additive_terminal_object
  C Prod t Add) T0 P A B X D b c h)) (@kernel_adjunction_family_func K C (@additive_preadditive C Prod t Add) t
  (@additive_terminal_object C Prod t Add) P (@transf_arrow_diagram_func K C B X b))
  (@one_cat_native_snake_kernel_first K C (@additive_preadditive C Prod t Add) C1 t (@additive_terminal_object C
  Prod t Add) T0 P Q A B X D b c h) (@one_cat_native_snake_six_term_result K C C1 Prod t Add T0 P Q N A B X D b
  c h)) (@finite_arrow_tail_rest (Functor_cat K C) (@OneCatNativeExactArrowPair K C (@additive_preadditive C
  Prod t Add) C1 t (@additive_terminal_object C Prod t Add) T0 P Q N) (succ (succ (succ zero)))
  (@kernel_adjunction_family_func K C (@additive_preadditive C Prod t Add) t (@additive_terminal_object C Prod t
  Add) P (@one_cat_native_snake_alpha_diagram K C (@additive_preadditive C Prod t Add) C1 t
  (@additive_terminal_object C Prod t Add) T0 P A B X D b c h)) (@kernel_adjunction_family_func K C
  (@additive_preadditive C Prod t Add) t (@additive_terminal_object C Prod t Add) P (@transf_arrow_diagram_func
  K C B X b)) (@one_cat_native_snake_kernel_first K C (@additive_preadditive C Prod t Add) C1 t
  (@additive_terminal_object C Prod t Add) T0 P Q A B X D b c h) (@one_cat_native_snake_six_term_result K C C1
  Prod t Add T0 P Q N A B X D b c h))) (@finite_arrow_tail_rest (Functor_cat K C) (@OneCatNativeExactArrowPair K
  C (@additive_preadditive C Prod t Add) C1 t (@additive_terminal_object C Prod t Add) T0 P Q N) (succ (succ
  zero)) (@kernel_adjunction_family_func K C (@additive_preadditive C Prod t Add) t (@additive_terminal_object C
  Prod t Add) P (@transf_arrow_diagram_func K C B X b)) (@finite_arrow_tail_next (Functor_cat K C)
  (@OneCatNativeExactArrowPair K C (@additive_preadditive C Prod t Add) C1 t (@additive_terminal_object C Prod t
  Add) T0 P Q N) (succ (succ (succ zero))) (@kernel_adjunction_family_func K C (@additive_preadditive C Prod t
  Add) t (@additive_terminal_object C Prod t Add) P (@one_cat_native_snake_alpha_diagram K C
  (@additive_preadditive C Prod t Add) C1 t (@additive_terminal_object C Prod t Add) T0 P A B X D b c h))
  (@kernel_adjunction_family_func K C (@additive_preadditive C Prod t Add) t (@additive_terminal_object C Prod t
  Add) P (@transf_arrow_diagram_func K C B X b)) (@one_cat_native_snake_kernel_first K C (@additive_preadditive
  C Prod t Add) C1 t (@additive_terminal_object C Prod t Add) T0 P Q A B X D b c h)
  (@one_cat_native_snake_six_term_result K C C1 Prod t Add T0 P Q N A B X D b c h)) (@finite_arrow_tail_arrow
  (Functor_cat K C) (@OneCatNativeExactArrowPair K C (@additive_preadditive C Prod t Add) C1 t
  (@additive_terminal_object C Prod t Add) T0 P Q N) (succ (succ (succ zero))) (@kernel_adjunction_family_func K
  C (@additive_preadditive C Prod t Add) t (@additive_terminal_object C Prod t Add) P
  (@one_cat_native_snake_alpha_diagram K C (@additive_preadditive C Prod t Add) C1 t (@additive_terminal_object
  C Prod t Add) T0 P A B X D b c h)) (@kernel_adjunction_family_func K C (@additive_preadditive C Prod t Add) t
  (@additive_terminal_object C Prod t Add) P (@transf_arrow_diagram_func K C B X b))
  (@one_cat_native_snake_kernel_first K C (@additive_preadditive C Prod t Add) C1 t (@additive_terminal_object C
  Prod t Add) T0 P Q A B X D b c h) (@one_cat_native_snake_six_term_result K C C1 Prod t Add T0 P Q N A B X D b
  c h)) (@finite_arrow_tail_rest (Functor_cat K C) (@OneCatNativeExactArrowPair K C (@additive_preadditive C
  Prod t Add) C1 t (@additive_terminal_object C Prod t Add) T0 P Q N) (succ (succ (succ zero)))
  (@kernel_adjunction_family_func K C (@additive_preadditive C Prod t Add) t (@additive_terminal_object C Prod t
  Add) P (@one_cat_native_snake_alpha_diagram K C (@additive_preadditive C Prod t Add) C1 t
  (@additive_terminal_object C Prod t Add) T0 P A B X D b c h)) (@kernel_adjunction_family_func K C
  (@additive_preadditive C Prod t Add) t (@additive_terminal_object C Prod t Add) P (@transf_arrow_diagram_func
  K C B X b)) (@one_cat_native_snake_kernel_first K C (@additive_preadditive C Prod t Add) C1 t
  (@additive_terminal_object C Prod t Add) T0 P Q A B X D b c h) (@one_cat_native_snake_six_term_result K C C1
  Prod t Add T0 P Q N A B X D b c h)))) (@finite_arrow_tail_next (Functor_cat K C) (@OneCatNativeExactArrowPair
  K C (@additive_preadditive C Prod t Add) C1 t (@additive_terminal_object C Prod t Add) T0 P Q N) zero
  (@finite_arrow_tail_next (Functor_cat K C) (@OneCatNativeExactArrowPair K C (@additive_preadditive C Prod t
  Add) C1 t (@additive_terminal_object C Prod t Add) T0 P Q N) (succ (succ zero))
  (@kernel_adjunction_family_func K C (@additive_preadditive C Prod t Add) t (@additive_terminal_object C Prod t
  Add) P (@transf_arrow_diagram_func K C B X b)) (@finite_arrow_tail_next (Functor_cat K C)
  (@OneCatNativeExactArrowPair K C (@additive_preadditive C Prod t Add) C1 t (@additive_terminal_object C Prod t
  Add) T0 P Q N) (succ (succ (succ zero))) (@kernel_adjunction_family_func K C (@additive_preadditive C Prod t
  Add) t (@additive_terminal_object C Prod t Add) P (@one_cat_native_snake_alpha_diagram K C
  (@additive_preadditive C Prod t Add) C1 t (@additive_terminal_object C Prod t Add) T0 P A B X D b c h))
  (@kernel_adjunction_family_func K C (@additive_preadditive C Prod t Add) t (@additive_terminal_object C Prod t
  Add) P (@transf_arrow_diagram_func K C B X b)) (@one_cat_native_snake_kernel_first K C (@additive_preadditive
  C Prod t Add) C1 t (@additive_terminal_object C Prod t Add) T0 P Q A B X D b c h)
  (@one_cat_native_snake_six_term_result K C C1 Prod t Add T0 P Q N A B X D b c h)) (@finite_arrow_tail_arrow
  (Functor_cat K C) (@OneCatNativeExactArrowPair K C (@additive_preadditive C Prod t Add) C1 t
  (@additive_terminal_object C Prod t Add) T0 P Q N) (succ (succ (succ zero))) (@kernel_adjunction_family_func K
  C (@additive_preadditive C Prod t Add) t (@additive_terminal_object C Prod t Add) P
  (@one_cat_native_snake_alpha_diagram K C (@additive_preadditive C Prod t Add) C1 t (@additive_terminal_object
  C Prod t Add) T0 P A B X D b c h)) (@kernel_adjunction_family_func K C (@additive_preadditive C Prod t Add) t
  (@additive_terminal_object C Prod t Add) P (@transf_arrow_diagram_func K C B X b))
  (@one_cat_native_snake_kernel_first K C (@additive_preadditive C Prod t Add) C1 t (@additive_terminal_object C
  Prod t Add) T0 P Q A B X D b c h) (@one_cat_native_snake_six_term_result K C C1 Prod t Add T0 P Q N A B X D b
  c h)) (@finite_arrow_tail_rest (Functor_cat K C) (@OneCatNativeExactArrowPair K C (@additive_preadditive C
  Prod t Add) C1 t (@additive_terminal_object C Prod t Add) T0 P Q N) (succ (succ (succ zero)))
  (@kernel_adjunction_family_func K C (@additive_preadditive C Prod t Add) t (@additive_terminal_object C Prod t
  Add) P (@one_cat_native_snake_alpha_diagram K C (@additive_preadditive C Prod t Add) C1 t
  (@additive_terminal_object C Prod t Add) T0 P A B X D b c h)) (@kernel_adjunction_family_func K C
  (@additive_preadditive C Prod t Add) t (@additive_terminal_object C Prod t Add) P (@transf_arrow_diagram_func
  K C B X b)) (@one_cat_native_snake_kernel_first K C (@additive_preadditive C Prod t Add) C1 t
  (@additive_terminal_object C Prod t Add) T0 P Q A B X D b c h) (@one_cat_native_snake_six_term_result K C C1
  Prod t Add T0 P Q N A B X D b c h))) (@finite_arrow_tail_next (Functor_cat K C) (@OneCatNativeExactArrowPair K
  C (@additive_preadditive C Prod t Add) C1 t (@additive_terminal_object C Prod t Add) T0 P Q N) (succ zero)
  (@finite_arrow_tail_next (Functor_cat K C) (@OneCatNativeExactArrowPair K C (@additive_preadditive C Prod t
  Add) C1 t (@additive_terminal_object C Prod t Add) T0 P Q N) (succ (succ (succ zero)))
  (@kernel_adjunction_family_func K C (@additive_preadditive C Prod t Add) t (@additive_terminal_object C Prod t
  Add) P (@one_cat_native_snake_alpha_diagram K C (@additive_preadditive C Prod t Add) C1 t
  (@additive_terminal_object C Prod t Add) T0 P A B X D b c h)) (@kernel_adjunction_family_func K C
  (@additive_preadditive C Prod t Add) t (@additive_terminal_object C Prod t Add) P (@transf_arrow_diagram_func
  K C B X b)) (@one_cat_native_snake_kernel_first K C (@additive_preadditive C Prod t Add) C1 t
  (@additive_terminal_object C Prod t Add) T0 P Q A B X D b c h) (@one_cat_native_snake_six_term_result K C C1
  Prod t Add T0 P Q N A B X D b c h)) (@finite_arrow_tail_next (Functor_cat K C) (@OneCatNativeExactArrowPair K
  C (@additive_preadditive C Prod t Add) C1 t (@additive_terminal_object C Prod t Add) T0 P Q N) (succ (succ
  zero)) (@kernel_adjunction_family_func K C (@additive_preadditive C Prod t Add) t (@additive_terminal_object C
  Prod t Add) P (@transf_arrow_diagram_func K C B X b)) (@finite_arrow_tail_next (Functor_cat K C)
  (@OneCatNativeExactArrowPair K C (@additive_preadditive C Prod t Add) C1 t (@additive_terminal_object C Prod t
  Add) T0 P Q N) (succ (succ (succ zero))) (@kernel_adjunction_family_func K C (@additive_preadditive C Prod t
  Add) t (@additive_terminal_object C Prod t Add) P (@one_cat_native_snake_alpha_diagram K C
  (@additive_preadditive C Prod t Add) C1 t (@additive_terminal_object C Prod t Add) T0 P A B X D b c h))
  (@kernel_adjunction_family_func K C (@additive_preadditive C Prod t Add) t (@additive_terminal_object C Prod t
  Add) P (@transf_arrow_diagram_func K C B X b)) (@one_cat_native_snake_kernel_first K C (@additive_preadditive
  C Prod t Add) C1 t (@additive_terminal_object C Prod t Add) T0 P Q A B X D b c h)
  (@one_cat_native_snake_six_term_result K C C1 Prod t Add T0 P Q N A B X D b c h)) (@finite_arrow_tail_arrow
  (Functor_cat K C) (@OneCatNativeExactArrowPair K C (@additive_preadditive C Prod t Add) C1 t
  (@additive_terminal_object C Prod t Add) T0 P Q N) (succ (succ (succ zero))) (@kernel_adjunction_family_func K
  C (@additive_preadditive C Prod t Add) t (@additive_terminal_object C Prod t Add) P
  (@one_cat_native_snake_alpha_diagram K C (@additive_preadditive C Prod t Add) C1 t (@additive_terminal_object
  C Prod t Add) T0 P A B X D b c h)) (@kernel_adjunction_family_func K C (@additive_preadditive C Prod t Add) t
  (@additive_terminal_object C Prod t Add) P (@transf_arrow_diagram_func K C B X b))
  (@one_cat_native_snake_kernel_first K C (@additive_preadditive C Prod t Add) C1 t (@additive_terminal_object C
  Prod t Add) T0 P Q A B X D b c h) (@one_cat_native_snake_six_term_result K C C1 Prod t Add T0 P Q N A B X D b
  c h)) (@finite_arrow_tail_rest (Functor_cat K C) (@OneCatNativeExactArrowPair K C (@additive_preadditive C
  Prod t Add) C1 t (@additive_terminal_object C Prod t Add) T0 P Q N) (succ (succ (succ zero)))
  (@kernel_adjunction_family_func K C (@additive_preadditive C Prod t Add) t (@additive_terminal_object C Prod t
  Add) P (@one_cat_native_snake_alpha_diagram K C (@additive_preadditive C Prod t Add) C1 t
  (@additive_terminal_object C Prod t Add) T0 P A B X D b c h)) (@kernel_adjunction_family_func K C
  (@additive_preadditive C Prod t Add) t (@additive_terminal_object C Prod t Add) P (@transf_arrow_diagram_func
  K C B X b)) (@one_cat_native_snake_kernel_first K C (@additive_preadditive C Prod t Add) C1 t
  (@additive_terminal_object C Prod t Add) T0 P Q A B X D b c h) (@one_cat_native_snake_six_term_result K C C1
  Prod t Add T0 P Q N A B X D b c h))) (@finite_arrow_tail_arrow (Functor_cat K C) (@OneCatNativeExactArrowPair
  K C (@additive_preadditive C Prod t Add) C1 t (@additive_terminal_object C Prod t Add) T0 P Q N) (succ (succ
  zero)) (@kernel_adjunction_family_func K C (@additive_preadditive C Prod t Add) t (@additive_terminal_object C
  Prod t Add) P (@transf_arrow_diagram_func K C B X b)) (@finite_arrow_tail_next (Functor_cat K C)
  (@OneCatNativeExactArrowPair K C (@additive_preadditive C Prod t Add) C1 t (@additive_terminal_object C Prod t
  Add) T0 P Q N) (succ (succ (succ zero))) (@kernel_adjunction_family_func K C (@additive_preadditive C Prod t
  Add) t (@additive_terminal_object C Prod t Add) P (@one_cat_native_snake_alpha_diagram K C
  (@additive_preadditive C Prod t Add) C1 t (@additive_terminal_object C Prod t Add) T0 P A B X D b c h))
  (@kernel_adjunction_family_func K C (@additive_preadditive C Prod t Add) t (@additive_terminal_object C Prod t
  Add) P (@transf_arrow_diagram_func K C B X b)) (@one_cat_native_snake_kernel_first K C (@additive_preadditive
  C Prod t Add) C1 t (@additive_terminal_object C Prod t Add) T0 P Q A B X D b c h)
  (@one_cat_native_snake_six_term_result K C C1 Prod t Add T0 P Q N A B X D b c h)) (@finite_arrow_tail_arrow
  (Functor_cat K C) (@OneCatNativeExactArrowPair K C (@additive_preadditive C Prod t Add) C1 t
  (@additive_terminal_object C Prod t Add) T0 P Q N) (succ (succ (succ zero))) (@kernel_adjunction_family_func K
  C (@additive_preadditive C Prod t Add) t (@additive_terminal_object C Prod t Add) P
  (@one_cat_native_snake_alpha_diagram K C (@additive_preadditive C Prod t Add) C1 t (@additive_terminal_object
  C Prod t Add) T0 P A B X D b c h)) (@kernel_adjunction_family_func K C (@additive_preadditive C Prod t Add) t
  (@additive_terminal_object C Prod t Add) P (@transf_arrow_diagram_func K C B X b))
  (@one_cat_native_snake_kernel_first K C (@additive_preadditive C Prod t Add) C1 t (@additive_terminal_object C
  Prod t Add) T0 P Q A B X D b c h) (@one_cat_native_snake_six_term_result K C C1 Prod t Add T0 P Q N A B X D b
  c h)) (@finite_arrow_tail_rest (Functor_cat K C) (@OneCatNativeExactArrowPair K C (@additive_preadditive C
  Prod t Add) C1 t (@additive_terminal_object C Prod t Add) T0 P Q N) (succ (succ (succ zero)))
  (@kernel_adjunction_family_func K C (@additive_preadditive C Prod t Add) t (@additive_terminal_object C Prod t
  Add) P (@one_cat_native_snake_alpha_diagram K C (@additive_preadditive C Prod t Add) C1 t
  (@additive_terminal_object C Prod t Add) T0 P A B X D b c h)) (@kernel_adjunction_family_func K C
  (@additive_preadditive C Prod t Add) t (@additive_terminal_object C Prod t Add) P (@transf_arrow_diagram_func
  K C B X b)) (@one_cat_native_snake_kernel_first K C (@additive_preadditive C Prod t Add) C1 t
  (@additive_terminal_object C Prod t Add) T0 P Q A B X D b c h) (@one_cat_native_snake_six_term_result K C C1
  Prod t Add T0 P Q N A B X D b c h))) (@finite_arrow_tail_rest (Functor_cat K C) (@OneCatNativeExactArrowPair K
  C (@additive_preadditive C Prod t Add) C1 t (@additive_terminal_object C Prod t Add) T0 P Q N) (succ (succ
  zero)) (@kernel_adjunction_family_func K C (@additive_preadditive C Prod t Add) t (@additive_terminal_object C
  Prod t Add) P (@transf_arrow_diagram_func K C B X b)) (@finite_arrow_tail_next (Functor_cat K C)
  (@OneCatNativeExactArrowPair K C (@additive_preadditive C Prod t Add) C1 t (@additive_terminal_object C Prod t
  Add) T0 P Q N) (succ (succ (succ zero))) (@kernel_adjunction_family_func K C (@additive_preadditive C Prod t
  Add) t (@additive_terminal_object C Prod t Add) P (@one_cat_native_snake_alpha_diagram K C
  (@additive_preadditive C Prod t Add) C1 t (@additive_terminal_object C Prod t Add) T0 P A B X D b c h))
  (@kernel_adjunction_family_func K C (@additive_preadditive C Prod t Add) t (@additive_terminal_object C Prod t
  Add) P (@transf_arrow_diagram_func K C B X b)) (@one_cat_native_snake_kernel_first K C (@additive_preadditive
  C Prod t Add) C1 t (@additive_terminal_object C Prod t Add) T0 P Q A B X D b c h)
  (@one_cat_native_snake_six_term_result K C C1 Prod t Add T0 P Q N A B X D b c h)) (@finite_arrow_tail_arrow
  (Functor_cat K C) (@OneCatNativeExactArrowPair K C (@additive_preadditive C Prod t Add) C1 t
  (@additive_terminal_object C Prod t Add) T0 P Q N) (succ (succ (succ zero))) (@kernel_adjunction_family_func K
  C (@additive_preadditive C Prod t Add) t (@additive_terminal_object C Prod t Add) P
  (@one_cat_native_snake_alpha_diagram K C (@additive_preadditive C Prod t Add) C1 t (@additive_terminal_object
  C Prod t Add) T0 P A B X D b c h)) (@kernel_adjunction_family_func K C (@additive_preadditive C Prod t Add) t
  (@additive_terminal_object C Prod t Add) P (@transf_arrow_diagram_func K C B X b))
  (@one_cat_native_snake_kernel_first K C (@additive_preadditive C Prod t Add) C1 t (@additive_terminal_object C
  Prod t Add) T0 P Q A B X D b c h) (@one_cat_native_snake_six_term_result K C C1 Prod t Add T0 P Q N A B X D b
  c h)) (@finite_arrow_tail_rest (Functor_cat K C) (@OneCatNativeExactArrowPair K C (@additive_preadditive C
  Prod t Add) C1 t (@additive_terminal_object C Prod t Add) T0 P Q N) (succ (succ (succ zero)))
  (@kernel_adjunction_family_func K C (@additive_preadditive C Prod t Add) t (@additive_terminal_object C Prod t
  Add) P (@one_cat_native_snake_alpha_diagram K C (@additive_preadditive C Prod t Add) C1 t
  (@additive_terminal_object C Prod t Add) T0 P A B X D b c h)) (@kernel_adjunction_family_func K C
  (@additive_preadditive C Prod t Add) t (@additive_terminal_object C Prod t Add) P (@transf_arrow_diagram_func
  K C B X b)) (@one_cat_native_snake_kernel_first K C (@additive_preadditive C Prod t Add) C1 t
  (@additive_terminal_object C Prod t Add) T0 P Q A B X D b c h) (@one_cat_native_snake_six_term_result K C C1
  Prod t Add T0 P Q N A B X D b c h)))) (@finite_arrow_tail_arrow (Functor_cat K C) (@OneCatNativeExactArrowPair
  K C (@additive_preadditive C Prod t Add) C1 t (@additive_terminal_object C Prod t Add) T0 P Q N) (succ zero)
  (@finite_arrow_tail_next (Functor_cat K C) (@OneCatNativeExactArrowPair K C (@additive_preadditive C Prod t
  Add) C1 t (@additive_terminal_object C Prod t Add) T0 P Q N) (succ (succ (succ zero)))
  (@kernel_adjunction_family_func K C (@additive_preadditive C Prod t Add) t (@additive_terminal_object C Prod t
  Add) P (@one_cat_native_snake_alpha_diagram K C (@additive_preadditive C Prod t Add) C1 t
  (@additive_terminal_object C Prod t Add) T0 P A B X D b c h)) (@kernel_adjunction_family_func K C
  (@additive_preadditive C Prod t Add) t (@additive_terminal_object C Prod t Add) P (@transf_arrow_diagram_func
  K C B X b)) (@one_cat_native_snake_kernel_first K C (@additive_preadditive C Prod t Add) C1 t
  (@additive_terminal_object C Prod t Add) T0 P Q A B X D b c h) (@one_cat_native_snake_six_term_result K C C1
  Prod t Add T0 P Q N A B X D b c h)) (@finite_arrow_tail_next (Functor_cat K C) (@OneCatNativeExactArrowPair K
  C (@additive_preadditive C Prod t Add) C1 t (@additive_terminal_object C Prod t Add) T0 P Q N) (succ (succ
  zero)) (@kernel_adjunction_family_func K C (@additive_preadditive C Prod t Add) t (@additive_terminal_object C
  Prod t Add) P (@transf_arrow_diagram_func K C B X b)) (@finite_arrow_tail_next (Functor_cat K C)
  (@OneCatNativeExactArrowPair K C (@additive_preadditive C Prod t Add) C1 t (@additive_terminal_object C Prod t
  Add) T0 P Q N) (succ (succ (succ zero))) (@kernel_adjunction_family_func K C (@additive_preadditive C Prod t
  Add) t (@additive_terminal_object C Prod t Add) P (@one_cat_native_snake_alpha_diagram K C
  (@additive_preadditive C Prod t Add) C1 t (@additive_terminal_object C Prod t Add) T0 P A B X D b c h))
  (@kernel_adjunction_family_func K C (@additive_preadditive C Prod t Add) t (@additive_terminal_object C Prod t
  Add) P (@transf_arrow_diagram_func K C B X b)) (@one_cat_native_snake_kernel_first K C (@additive_preadditive
  C Prod t Add) C1 t (@additive_terminal_object C Prod t Add) T0 P Q A B X D b c h)
  (@one_cat_native_snake_six_term_result K C C1 Prod t Add T0 P Q N A B X D b c h)) (@finite_arrow_tail_arrow
  (Functor_cat K C) (@OneCatNativeExactArrowPair K C (@additive_preadditive C Prod t Add) C1 t
  (@additive_terminal_object C Prod t Add) T0 P Q N) (succ (succ (succ zero))) (@kernel_adjunction_family_func K
  C (@additive_preadditive C Prod t Add) t (@additive_terminal_object C Prod t Add) P
  (@one_cat_native_snake_alpha_diagram K C (@additive_preadditive C Prod t Add) C1 t (@additive_terminal_object
  C Prod t Add) T0 P A B X D b c h)) (@kernel_adjunction_family_func K C (@additive_preadditive C Prod t Add) t
  (@additive_terminal_object C Prod t Add) P (@transf_arrow_diagram_func K C B X b))
  (@one_cat_native_snake_kernel_first K C (@additive_preadditive C Prod t Add) C1 t (@additive_terminal_object C
  Prod t Add) T0 P Q A B X D b c h) (@one_cat_native_snake_six_term_result K C C1 Prod t Add T0 P Q N A B X D b
  c h)) (@finite_arrow_tail_rest (Functor_cat K C) (@OneCatNativeExactArrowPair K C (@additive_preadditive C
  Prod t Add) C1 t (@additive_terminal_object C Prod t Add) T0 P Q N) (succ (succ (succ zero)))
  (@kernel_adjunction_family_func K C (@additive_preadditive C Prod t Add) t (@additive_terminal_object C Prod t
  Add) P (@one_cat_native_snake_alpha_diagram K C (@additive_preadditive C Prod t Add) C1 t
  (@additive_terminal_object C Prod t Add) T0 P A B X D b c h)) (@kernel_adjunction_family_func K C
  (@additive_preadditive C Prod t Add) t (@additive_terminal_object C Prod t Add) P (@transf_arrow_diagram_func
  K C B X b)) (@one_cat_native_snake_kernel_first K C (@additive_preadditive C Prod t Add) C1 t
  (@additive_terminal_object C Prod t Add) T0 P Q A B X D b c h) (@one_cat_native_snake_six_term_result K C C1
  Prod t Add T0 P Q N A B X D b c h))) (@finite_arrow_tail_arrow (Functor_cat K C) (@OneCatNativeExactArrowPair
  K C (@additive_preadditive C Prod t Add) C1 t (@additive_terminal_object C Prod t Add) T0 P Q N) (succ (succ
  zero)) (@kernel_adjunction_family_func K C (@additive_preadditive C Prod t Add) t (@additive_terminal_object C
  Prod t Add) P (@transf_arrow_diagram_func K C B X b)) (@finite_arrow_tail_next (Functor_cat K C)
  (@OneCatNativeExactArrowPair K C (@additive_preadditive C Prod t Add) C1 t (@additive_terminal_object C Prod t
  Add) T0 P Q N) (succ (succ (succ zero))) (@kernel_adjunction_family_func K C (@additive_preadditive C Prod t
  Add) t (@additive_terminal_object C Prod t Add) P (@one_cat_native_snake_alpha_diagram K C
  (@additive_preadditive C Prod t Add) C1 t (@additive_terminal_object C Prod t Add) T0 P A B X D b c h))
  (@kernel_adjunction_family_func K C (@additive_preadditive C Prod t Add) t (@additive_terminal_object C Prod t
  Add) P (@transf_arrow_diagram_func K C B X b)) (@one_cat_native_snake_kernel_first K C (@additive_preadditive
  C Prod t Add) C1 t (@additive_terminal_object C Prod t Add) T0 P Q A B X D b c h)
  (@one_cat_native_snake_six_term_result K C C1 Prod t Add T0 P Q N A B X D b c h)) (@finite_arrow_tail_arrow
  (Functor_cat K C) (@OneCatNativeExactArrowPair K C (@additive_preadditive C Prod t Add) C1 t
  (@additive_terminal_object C Prod t Add) T0 P Q N) (succ (succ (succ zero))) (@kernel_adjunction_family_func K
  C (@additive_preadditive C Prod t Add) t (@additive_terminal_object C Prod t Add) P
  (@one_cat_native_snake_alpha_diagram K C (@additive_preadditive C Prod t Add) C1 t (@additive_terminal_object
  C Prod t Add) T0 P A B X D b c h)) (@kernel_adjunction_family_func K C (@additive_preadditive C Prod t Add) t
  (@additive_terminal_object C Prod t Add) P (@transf_arrow_diagram_func K C B X b))
  (@one_cat_native_snake_kernel_first K C (@additive_preadditive C Prod t Add) C1 t (@additive_terminal_object C
  Prod t Add) T0 P Q A B X D b c h) (@one_cat_native_snake_six_term_result K C C1 Prod t Add T0 P Q N A B X D b
  c h)) (@finite_arrow_tail_rest (Functor_cat K C) (@OneCatNativeExactArrowPair K C (@additive_preadditive C
  Prod t Add) C1 t (@additive_terminal_object C Prod t Add) T0 P Q N) (succ (succ (succ zero)))
  (@kernel_adjunction_family_func K C (@additive_preadditive C Prod t Add) t (@additive_terminal_object C Prod t
  Add) P (@one_cat_native_snake_alpha_diagram K C (@additive_preadditive C Prod t Add) C1 t
  (@additive_terminal_object C Prod t Add) T0 P A B X D b c h)) (@kernel_adjunction_family_func K C
  (@additive_preadditive C Prod t Add) t (@additive_terminal_object C Prod t Add) P (@transf_arrow_diagram_func
  K C B X b)) (@one_cat_native_snake_kernel_first K C (@additive_preadditive C Prod t Add) C1 t
  (@additive_terminal_object C Prod t Add) T0 P Q A B X D b c h) (@one_cat_native_snake_six_term_result K C C1
  Prod t Add T0 P Q N A B X D b c h))) (@finite_arrow_tail_rest (Functor_cat K C) (@OneCatNativeExactArrowPair K
  C (@additive_preadditive C Prod t Add) C1 t (@additive_terminal_object C Prod t Add) T0 P Q N) (succ (succ
  zero)) (@kernel_adjunction_family_func K C (@additive_preadditive C Prod t Add) t (@additive_terminal_object C
  Prod t Add) P (@transf_arrow_diagram_func K C B X b)) (@finite_arrow_tail_next (Functor_cat K C)
  (@OneCatNativeExactArrowPair K C (@additive_preadditive C Prod t Add) C1 t (@additive_terminal_object C Prod t
  Add) T0 P Q N) (succ (succ (succ zero))) (@kernel_adjunction_family_func K C (@additive_preadditive C Prod t
  Add) t (@additive_terminal_object C Prod t Add) P (@one_cat_native_snake_alpha_diagram K C
  (@additive_preadditive C Prod t Add) C1 t (@additive_terminal_object C Prod t Add) T0 P A B X D b c h))
  (@kernel_adjunction_family_func K C (@additive_preadditive C Prod t Add) t (@additive_terminal_object C Prod t
  Add) P (@transf_arrow_diagram_func K C B X b)) (@one_cat_native_snake_kernel_first K C (@additive_preadditive
  C Prod t Add) C1 t (@additive_terminal_object C Prod t Add) T0 P Q A B X D b c h)
  (@one_cat_native_snake_six_term_result K C C1 Prod t Add T0 P Q N A B X D b c h)) (@finite_arrow_tail_arrow
  (Functor_cat K C) (@OneCatNativeExactArrowPair K C (@additive_preadditive C Prod t Add) C1 t
  (@additive_terminal_object C Prod t Add) T0 P Q N) (succ (succ (succ zero))) (@kernel_adjunction_family_func K
  C (@additive_preadditive C Prod t Add) t (@additive_terminal_object C Prod t Add) P
  (@one_cat_native_snake_alpha_diagram K C (@additive_preadditive C Prod t Add) C1 t (@additive_terminal_object
  C Prod t Add) T0 P A B X D b c h)) (@kernel_adjunction_family_func K C (@additive_preadditive C Prod t Add) t
  (@additive_terminal_object C Prod t Add) P (@transf_arrow_diagram_func K C B X b))
  (@one_cat_native_snake_kernel_first K C (@additive_preadditive C Prod t Add) C1 t (@additive_terminal_object C
  Prod t Add) T0 P Q A B X D b c h) (@one_cat_native_snake_six_term_result K C C1 Prod t Add T0 P Q N A B X D b
  c h)) (@finite_arrow_tail_rest (Functor_cat K C) (@OneCatNativeExactArrowPair K C (@additive_preadditive C
  Prod t Add) C1 t (@additive_terminal_object C Prod t Add) T0 P Q N) (succ (succ (succ zero)))
  (@kernel_adjunction_family_func K C (@additive_preadditive C Prod t Add) t (@additive_terminal_object C Prod t
  Add) P (@one_cat_native_snake_alpha_diagram K C (@additive_preadditive C Prod t Add) C1 t
  (@additive_terminal_object C Prod t Add) T0 P A B X D b c h)) (@kernel_adjunction_family_func K C
  (@additive_preadditive C Prod t Add) t (@additive_terminal_object C Prod t Add) P (@transf_arrow_diagram_func
  K C B X b)) (@one_cat_native_snake_kernel_first K C (@additive_preadditive C Prod t Add) C1 t
  (@additive_terminal_object C Prod t Add) T0 P Q A B X D b c h) (@one_cat_native_snake_six_term_result K C C1
  Prod t Add T0 P Q N A B X D b c h)))) (@finite_arrow_tail_rest (Functor_cat K C) (@OneCatNativeExactArrowPair
  K C (@additive_preadditive C Prod t Add) C1 t (@additive_terminal_object C Prod t Add) T0 P Q N) (succ zero)
  (@finite_arrow_tail_next (Functor_cat K C) (@OneCatNativeExactArrowPair K C (@additive_preadditive C Prod t
  Add) C1 t (@additive_terminal_object C Prod t Add) T0 P Q N) (succ (succ (succ zero)))
  (@kernel_adjunction_family_func K C (@additive_preadditive C Prod t Add) t (@additive_terminal_object C Prod t
  Add) P (@one_cat_native_snake_alpha_diagram K C (@additive_preadditive C Prod t Add) C1 t
  (@additive_terminal_object C Prod t Add) T0 P A B X D b c h)) (@kernel_adjunction_family_func K C
  (@additive_preadditive C Prod t Add) t (@additive_terminal_object C Prod t Add) P (@transf_arrow_diagram_func
  K C B X b)) (@one_cat_native_snake_kernel_first K C (@additive_preadditive C Prod t Add) C1 t
  (@additive_terminal_object C Prod t Add) T0 P Q A B X D b c h) (@one_cat_native_snake_six_term_result K C C1
  Prod t Add T0 P Q N A B X D b c h)) (@finite_arrow_tail_next (Functor_cat K C) (@OneCatNativeExactArrowPair K
  C (@additive_preadditive C Prod t Add) C1 t (@additive_terminal_object C Prod t Add) T0 P Q N) (succ (succ
  zero)) (@kernel_adjunction_family_func K C (@additive_preadditive C Prod t Add) t (@additive_terminal_object C
  Prod t Add) P (@transf_arrow_diagram_func K C B X b)) (@finite_arrow_tail_next (Functor_cat K C)
  (@OneCatNativeExactArrowPair K C (@additive_preadditive C Prod t Add) C1 t (@additive_terminal_object C Prod t
  Add) T0 P Q N) (succ (succ (succ zero))) (@kernel_adjunction_family_func K C (@additive_preadditive C Prod t
  Add) t (@additive_terminal_object C Prod t Add) P (@one_cat_native_snake_alpha_diagram K C
  (@additive_preadditive C Prod t Add) C1 t (@additive_terminal_object C Prod t Add) T0 P A B X D b c h))
  (@kernel_adjunction_family_func K C (@additive_preadditive C Prod t Add) t (@additive_terminal_object C Prod t
  Add) P (@transf_arrow_diagram_func K C B X b)) (@one_cat_native_snake_kernel_first K C (@additive_preadditive
  C Prod t Add) C1 t (@additive_terminal_object C Prod t Add) T0 P Q A B X D b c h)
  (@one_cat_native_snake_six_term_result K C C1 Prod t Add T0 P Q N A B X D b c h)) (@finite_arrow_tail_arrow
  (Functor_cat K C) (@OneCatNativeExactArrowPair K C (@additive_preadditive C Prod t Add) C1 t
  (@additive_terminal_object C Prod t Add) T0 P Q N) (succ (succ (succ zero))) (@kernel_adjunction_family_func K
  C (@additive_preadditive C Prod t Add) t (@additive_terminal_object C Prod t Add) P
  (@one_cat_native_snake_alpha_diagram K C (@additive_preadditive C Prod t Add) C1 t (@additive_terminal_object
  C Prod t Add) T0 P A B X D b c h)) (@kernel_adjunction_family_func K C (@additive_preadditive C Prod t Add) t
  (@additive_terminal_object C Prod t Add) P (@transf_arrow_diagram_func K C B X b))
  (@one_cat_native_snake_kernel_first K C (@additive_preadditive C Prod t Add) C1 t (@additive_terminal_object C
  Prod t Add) T0 P Q A B X D b c h) (@one_cat_native_snake_six_term_result K C C1 Prod t Add T0 P Q N A B X D b
  c h)) (@finite_arrow_tail_rest (Functor_cat K C) (@OneCatNativeExactArrowPair K C (@additive_preadditive C
  Prod t Add) C1 t (@additive_terminal_object C Prod t Add) T0 P Q N) (succ (succ (succ zero)))
  (@kernel_adjunction_family_func K C (@additive_preadditive C Prod t Add) t (@additive_terminal_object C Prod t
  Add) P (@one_cat_native_snake_alpha_diagram K C (@additive_preadditive C Prod t Add) C1 t
  (@additive_terminal_object C Prod t Add) T0 P A B X D b c h)) (@kernel_adjunction_family_func K C
  (@additive_preadditive C Prod t Add) t (@additive_terminal_object C Prod t Add) P (@transf_arrow_diagram_func
  K C B X b)) (@one_cat_native_snake_kernel_first K C (@additive_preadditive C Prod t Add) C1 t
  (@additive_terminal_object C Prod t Add) T0 P Q A B X D b c h) (@one_cat_native_snake_six_term_result K C C1
  Prod t Add T0 P Q N A B X D b c h))) (@finite_arrow_tail_arrow (Functor_cat K C) (@OneCatNativeExactArrowPair
  K C (@additive_preadditive C Prod t Add) C1 t (@additive_terminal_object C Prod t Add) T0 P Q N) (succ (succ
  zero)) (@kernel_adjunction_family_func K C (@additive_preadditive C Prod t Add) t (@additive_terminal_object C
  Prod t Add) P (@transf_arrow_diagram_func K C B X b)) (@finite_arrow_tail_next (Functor_cat K C)
  (@OneCatNativeExactArrowPair K C (@additive_preadditive C Prod t Add) C1 t (@additive_terminal_object C Prod t
  Add) T0 P Q N) (succ (succ (succ zero))) (@kernel_adjunction_family_func K C (@additive_preadditive C Prod t
  Add) t (@additive_terminal_object C Prod t Add) P (@one_cat_native_snake_alpha_diagram K C
  (@additive_preadditive C Prod t Add) C1 t (@additive_terminal_object C Prod t Add) T0 P A B X D b c h))
  (@kernel_adjunction_family_func K C (@additive_preadditive C Prod t Add) t (@additive_terminal_object C Prod t
  Add) P (@transf_arrow_diagram_func K C B X b)) (@one_cat_native_snake_kernel_first K C (@additive_preadditive
  C Prod t Add) C1 t (@additive_terminal_object C Prod t Add) T0 P Q A B X D b c h)
  (@one_cat_native_snake_six_term_result K C C1 Prod t Add T0 P Q N A B X D b c h)) (@finite_arrow_tail_arrow
  (Functor_cat K C) (@OneCatNativeExactArrowPair K C (@additive_preadditive C Prod t Add) C1 t
  (@additive_terminal_object C Prod t Add) T0 P Q N) (succ (succ (succ zero))) (@kernel_adjunction_family_func K
  C (@additive_preadditive C Prod t Add) t (@additive_terminal_object C Prod t Add) P
  (@one_cat_native_snake_alpha_diagram K C (@additive_preadditive C Prod t Add) C1 t (@additive_terminal_object
  C Prod t Add) T0 P A B X D b c h)) (@kernel_adjunction_family_func K C (@additive_preadditive C Prod t Add) t
  (@additive_terminal_object C Prod t Add) P (@transf_arrow_diagram_func K C B X b))
  (@one_cat_native_snake_kernel_first K C (@additive_preadditive C Prod t Add) C1 t (@additive_terminal_object C
  Prod t Add) T0 P Q A B X D b c h) (@one_cat_native_snake_six_term_result K C C1 Prod t Add T0 P Q N A B X D b
  c h)) (@finite_arrow_tail_rest (Functor_cat K C) (@OneCatNativeExactArrowPair K C (@additive_preadditive C
  Prod t Add) C1 t (@additive_terminal_object C Prod t Add) T0 P Q N) (succ (succ (succ zero)))
  (@kernel_adjunction_family_func K C (@additive_preadditive C Prod t Add) t (@additive_terminal_object C Prod t
  Add) P (@one_cat_native_snake_alpha_diagram K C (@additive_preadditive C Prod t Add) C1 t
  (@additive_terminal_object C Prod t Add) T0 P A B X D b c h)) (@kernel_adjunction_family_func K C
  (@additive_preadditive C Prod t Add) t (@additive_terminal_object C Prod t Add) P (@transf_arrow_diagram_func
  K C B X b)) (@one_cat_native_snake_kernel_first K C (@additive_preadditive C Prod t Add) C1 t
  (@additive_terminal_object C Prod t Add) T0 P Q A B X D b c h) (@one_cat_native_snake_six_term_result K C C1
  Prod t Add T0 P Q N A B X D b c h))) (@finite_arrow_tail_rest (Functor_cat K C) (@OneCatNativeExactArrowPair K
  C (@additive_preadditive C Prod t Add) C1 t (@additive_terminal_object C Prod t Add) T0 P Q N) (succ (succ
  zero)) (@kernel_adjunction_family_func K C (@additive_preadditive C Prod t Add) t (@additive_terminal_object C
  Prod t Add) P (@transf_arrow_diagram_func K C B X b)) (@finite_arrow_tail_next (Functor_cat K C)
  (@OneCatNativeExactArrowPair K C (@additive_preadditive C Prod t Add) C1 t (@additive_terminal_object C Prod t
  Add) T0 P Q N) (succ (succ (succ zero))) (@kernel_adjunction_family_func K C (@additive_preadditive C Prod t
  Add) t (@additive_terminal_object C Prod t Add) P (@one_cat_native_snake_alpha_diagram K C
  (@additive_preadditive C Prod t Add) C1 t (@additive_terminal_object C Prod t Add) T0 P A B X D b c h))
  (@kernel_adjunction_family_func K C (@additive_preadditive C Prod t Add) t (@additive_terminal_object C Prod t
  Add) P (@transf_arrow_diagram_func K C B X b)) (@one_cat_native_snake_kernel_first K C (@additive_preadditive
  C Prod t Add) C1 t (@additive_terminal_object C Prod t Add) T0 P Q A B X D b c h)
  (@one_cat_native_snake_six_term_result K C C1 Prod t Add T0 P Q N A B X D b c h)) (@finite_arrow_tail_arrow
  (Functor_cat K C) (@OneCatNativeExactArrowPair K C (@additive_preadditive C Prod t Add) C1 t
  (@additive_terminal_object C Prod t Add) T0 P Q N) (succ (succ (succ zero))) (@kernel_adjunction_family_func K
  C (@additive_preadditive C Prod t Add) t (@additive_terminal_object C Prod t Add) P
  (@one_cat_native_snake_alpha_diagram K C (@additive_preadditive C Prod t Add) C1 t (@additive_terminal_object
  C Prod t Add) T0 P A B X D b c h)) (@kernel_adjunction_family_func K C (@additive_preadditive C Prod t Add) t
  (@additive_terminal_object C Prod t Add) P (@transf_arrow_diagram_func K C B X b))
  (@one_cat_native_snake_kernel_first K C (@additive_preadditive C Prod t Add) C1 t (@additive_terminal_object C
  Prod t Add) T0 P Q A B X D b c h) (@one_cat_native_snake_six_term_result K C C1 Prod t Add T0 P Q N A B X D b
  c h)) (@finite_arrow_tail_rest (Functor_cat K C) (@OneCatNativeExactArrowPair K C (@additive_preadditive C
  Prod t Add) C1 t (@additive_terminal_object C Prod t Add) T0 P Q N) (succ (succ (succ zero)))
  (@kernel_adjunction_family_func K C (@additive_preadditive C Prod t Add) t (@additive_terminal_object C Prod t
  Add) P (@one_cat_native_snake_alpha_diagram K C (@additive_preadditive C Prod t Add) C1 t
  (@additive_terminal_object C Prod t Add) T0 P A B X D b c h)) (@kernel_adjunction_family_func K C
  (@additive_preadditive C Prod t Add) t (@additive_terminal_object C Prod t Add) P (@transf_arrow_diagram_func
  K C B X b)) (@one_cat_native_snake_kernel_first K C (@additive_preadditive C Prod t Add) C1 t
  (@additive_terminal_object C Prod t Add) T0 P Q A B X D b c h) (@one_cat_native_snake_six_term_result K C C1
  Prod t Add T0 P Q N A B X D b c h))))) (@finite_arrow_tail_arrow (Functor_cat K C)
  (@OneCatNativeExactArrowPair K C (@additive_preadditive C Prod t Add) C1 t (@additive_terminal_object C Prod t
  Add) T0 P Q N) zero (@finite_arrow_tail_next (Functor_cat K C) (@OneCatNativeExactArrowPair K C
  (@additive_preadditive C Prod t Add) C1 t (@additive_terminal_object C Prod t Add) T0 P Q N) (succ (succ
  zero)) (@kernel_adjunction_family_func K C (@additive_preadditive C Prod t Add) t (@additive_terminal_object C
  Prod t Add) P (@transf_arrow_diagram_func K C B X b)) (@finite_arrow_tail_next (Functor_cat K C)
  (@OneCatNativeExactArrowPair K C (@additive_preadditive C Prod t Add) C1 t (@additive_terminal_object C Prod t
  Add) T0 P Q N) (succ (succ (succ zero))) (@kernel_adjunction_family_func K C (@additive_preadditive C Prod t
  Add) t (@additive_terminal_object C Prod t Add) P (@one_cat_native_snake_alpha_diagram K C
  (@additive_preadditive C Prod t Add) C1 t (@additive_terminal_object C Prod t Add) T0 P A B X D b c h))
  (@kernel_adjunction_family_func K C (@additive_preadditive C Prod t Add) t (@additive_terminal_object C Prod t
  Add) P (@transf_arrow_diagram_func K C B X b)) (@one_cat_native_snake_kernel_first K C (@additive_preadditive
  C Prod t Add) C1 t (@additive_terminal_object C Prod t Add) T0 P Q A B X D b c h)
  (@one_cat_native_snake_six_term_result K C C1 Prod t Add T0 P Q N A B X D b c h)) (@finite_arrow_tail_arrow
  (Functor_cat K C) (@OneCatNativeExactArrowPair K C (@additive_preadditive C Prod t Add) C1 t
  (@additive_terminal_object C Prod t Add) T0 P Q N) (succ (succ (succ zero))) (@kernel_adjunction_family_func K
  C (@additive_preadditive C Prod t Add) t (@additive_terminal_object C Prod t Add) P
  (@one_cat_native_snake_alpha_diagram K C (@additive_preadditive C Prod t Add) C1 t (@additive_terminal_object
  C Prod t Add) T0 P A B X D b c h)) (@kernel_adjunction_family_func K C (@additive_preadditive C Prod t Add) t
  (@additive_terminal_object C Prod t Add) P (@transf_arrow_diagram_func K C B X b))
  (@one_cat_native_snake_kernel_first K C (@additive_preadditive C Prod t Add) C1 t (@additive_terminal_object C
  Prod t Add) T0 P Q A B X D b c h) (@one_cat_native_snake_six_term_result K C C1 Prod t Add T0 P Q N A B X D b
  c h)) (@finite_arrow_tail_rest (Functor_cat K C) (@OneCatNativeExactArrowPair K C (@additive_preadditive C
  Prod t Add) C1 t (@additive_terminal_object C Prod t Add) T0 P Q N) (succ (succ (succ zero)))
  (@kernel_adjunction_family_func K C (@additive_preadditive C Prod t Add) t (@additive_terminal_object C Prod t
  Add) P (@one_cat_native_snake_alpha_diagram K C (@additive_preadditive C Prod t Add) C1 t
  (@additive_terminal_object C Prod t Add) T0 P A B X D b c h)) (@kernel_adjunction_family_func K C
  (@additive_preadditive C Prod t Add) t (@additive_terminal_object C Prod t Add) P (@transf_arrow_diagram_func
  K C B X b)) (@one_cat_native_snake_kernel_first K C (@additive_preadditive C Prod t Add) C1 t
  (@additive_terminal_object C Prod t Add) T0 P Q A B X D b c h) (@one_cat_native_snake_six_term_result K C C1
  Prod t Add T0 P Q N A B X D b c h))) (@finite_arrow_tail_next (Functor_cat K C) (@OneCatNativeExactArrowPair K
  C (@additive_preadditive C Prod t Add) C1 t (@additive_terminal_object C Prod t Add) T0 P Q N) (succ zero)
  (@finite_arrow_tail_next (Functor_cat K C) (@OneCatNativeExactArrowPair K C (@additive_preadditive C Prod t
  Add) C1 t (@additive_terminal_object C Prod t Add) T0 P Q N) (succ (succ (succ zero)))
  (@kernel_adjunction_family_func K C (@additive_preadditive C Prod t Add) t (@additive_terminal_object C Prod t
  Add) P (@one_cat_native_snake_alpha_diagram K C (@additive_preadditive C Prod t Add) C1 t
  (@additive_terminal_object C Prod t Add) T0 P A B X D b c h)) (@kernel_adjunction_family_func K C
  (@additive_preadditive C Prod t Add) t (@additive_terminal_object C Prod t Add) P (@transf_arrow_diagram_func
  K C B X b)) (@one_cat_native_snake_kernel_first K C (@additive_preadditive C Prod t Add) C1 t
  (@additive_terminal_object C Prod t Add) T0 P Q A B X D b c h) (@one_cat_native_snake_six_term_result K C C1
  Prod t Add T0 P Q N A B X D b c h)) (@finite_arrow_tail_next (Functor_cat K C) (@OneCatNativeExactArrowPair K
  C (@additive_preadditive C Prod t Add) C1 t (@additive_terminal_object C Prod t Add) T0 P Q N) (succ (succ
  zero)) (@kernel_adjunction_family_func K C (@additive_preadditive C Prod t Add) t (@additive_terminal_object C
  Prod t Add) P (@transf_arrow_diagram_func K C B X b)) (@finite_arrow_tail_next (Functor_cat K C)
  (@OneCatNativeExactArrowPair K C (@additive_preadditive C Prod t Add) C1 t (@additive_terminal_object C Prod t
  Add) T0 P Q N) (succ (succ (succ zero))) (@kernel_adjunction_family_func K C (@additive_preadditive C Prod t
  Add) t (@additive_terminal_object C Prod t Add) P (@one_cat_native_snake_alpha_diagram K C
  (@additive_preadditive C Prod t Add) C1 t (@additive_terminal_object C Prod t Add) T0 P A B X D b c h))
  (@kernel_adjunction_family_func K C (@additive_preadditive C Prod t Add) t (@additive_terminal_object C Prod t
  Add) P (@transf_arrow_diagram_func K C B X b)) (@one_cat_native_snake_kernel_first K C (@additive_preadditive
  C Prod t Add) C1 t (@additive_terminal_object C Prod t Add) T0 P Q A B X D b c h)
  (@one_cat_native_snake_six_term_result K C C1 Prod t Add T0 P Q N A B X D b c h)) (@finite_arrow_tail_arrow
  (Functor_cat K C) (@OneCatNativeExactArrowPair K C (@additive_preadditive C Prod t Add) C1 t
  (@additive_terminal_object C Prod t Add) T0 P Q N) (succ (succ (succ zero))) (@kernel_adjunction_family_func K
  C (@additive_preadditive C Prod t Add) t (@additive_terminal_object C Prod t Add) P
  (@one_cat_native_snake_alpha_diagram K C (@additive_preadditive C Prod t Add) C1 t (@additive_terminal_object
  C Prod t Add) T0 P A B X D b c h)) (@kernel_adjunction_family_func K C (@additive_preadditive C Prod t Add) t
  (@additive_terminal_object C Prod t Add) P (@transf_arrow_diagram_func K C B X b))
  (@one_cat_native_snake_kernel_first K C (@additive_preadditive C Prod t Add) C1 t (@additive_terminal_object C
  Prod t Add) T0 P Q A B X D b c h) (@one_cat_native_snake_six_term_result K C C1 Prod t Add T0 P Q N A B X D b
  c h)) (@finite_arrow_tail_rest (Functor_cat K C) (@OneCatNativeExactArrowPair K C (@additive_preadditive C
  Prod t Add) C1 t (@additive_terminal_object C Prod t Add) T0 P Q N) (succ (succ (succ zero)))
  (@kernel_adjunction_family_func K C (@additive_preadditive C Prod t Add) t (@additive_terminal_object C Prod t
  Add) P (@one_cat_native_snake_alpha_diagram K C (@additive_preadditive C Prod t Add) C1 t
  (@additive_terminal_object C Prod t Add) T0 P A B X D b c h)) (@kernel_adjunction_family_func K C
  (@additive_preadditive C Prod t Add) t (@additive_terminal_object C Prod t Add) P (@transf_arrow_diagram_func
  K C B X b)) (@one_cat_native_snake_kernel_first K C (@additive_preadditive C Prod t Add) C1 t
  (@additive_terminal_object C Prod t Add) T0 P Q A B X D b c h) (@one_cat_native_snake_six_term_result K C C1
  Prod t Add T0 P Q N A B X D b c h))) (@finite_arrow_tail_arrow (Functor_cat K C) (@OneCatNativeExactArrowPair
  K C (@additive_preadditive C Prod t Add) C1 t (@additive_terminal_object C Prod t Add) T0 P Q N) (succ (succ
  zero)) (@kernel_adjunction_family_func K C (@additive_preadditive C Prod t Add) t (@additive_terminal_object C
  Prod t Add) P (@transf_arrow_diagram_func K C B X b)) (@finite_arrow_tail_next (Functor_cat K C)
  (@OneCatNativeExactArrowPair K C (@additive_preadditive C Prod t Add) C1 t (@additive_terminal_object C Prod t
  Add) T0 P Q N) (succ (succ (succ zero))) (@kernel_adjunction_family_func K C (@additive_preadditive C Prod t
  Add) t (@additive_terminal_object C Prod t Add) P (@one_cat_native_snake_alpha_diagram K C
  (@additive_preadditive C Prod t Add) C1 t (@additive_terminal_object C Prod t Add) T0 P A B X D b c h))
  (@kernel_adjunction_family_func K C (@additive_preadditive C Prod t Add) t (@additive_terminal_object C Prod t
  Add) P (@transf_arrow_diagram_func K C B X b)) (@one_cat_native_snake_kernel_first K C (@additive_preadditive
  C Prod t Add) C1 t (@additive_terminal_object C Prod t Add) T0 P Q A B X D b c h)
  (@one_cat_native_snake_six_term_result K C C1 Prod t Add T0 P Q N A B X D b c h)) (@finite_arrow_tail_arrow
  (Functor_cat K C) (@OneCatNativeExactArrowPair K C (@additive_preadditive C Prod t Add) C1 t
  (@additive_terminal_object C Prod t Add) T0 P Q N) (succ (succ (succ zero))) (@kernel_adjunction_family_func K
  C (@additive_preadditive C Prod t Add) t (@additive_terminal_object C Prod t Add) P
  (@one_cat_native_snake_alpha_diagram K C (@additive_preadditive C Prod t Add) C1 t (@additive_terminal_object
  C Prod t Add) T0 P A B X D b c h)) (@kernel_adjunction_family_func K C (@additive_preadditive C Prod t Add) t
  (@additive_terminal_object C Prod t Add) P (@transf_arrow_diagram_func K C B X b))
  (@one_cat_native_snake_kernel_first K C (@additive_preadditive C Prod t Add) C1 t (@additive_terminal_object C
  Prod t Add) T0 P Q A B X D b c h) (@one_cat_native_snake_six_term_result K C C1 Prod t Add T0 P Q N A B X D b
  c h)) (@finite_arrow_tail_rest (Functor_cat K C) (@OneCatNativeExactArrowPair K C (@additive_preadditive C
  Prod t Add) C1 t (@additive_terminal_object C Prod t Add) T0 P Q N) (succ (succ (succ zero)))
  (@kernel_adjunction_family_func K C (@additive_preadditive C Prod t Add) t (@additive_terminal_object C Prod t
  Add) P (@one_cat_native_snake_alpha_diagram K C (@additive_preadditive C Prod t Add) C1 t
  (@additive_terminal_object C Prod t Add) T0 P A B X D b c h)) (@kernel_adjunction_family_func K C
  (@additive_preadditive C Prod t Add) t (@additive_terminal_object C Prod t Add) P (@transf_arrow_diagram_func
  K C B X b)) (@one_cat_native_snake_kernel_first K C (@additive_preadditive C Prod t Add) C1 t
  (@additive_terminal_object C Prod t Add) T0 P Q A B X D b c h) (@one_cat_native_snake_six_term_result K C C1
  Prod t Add T0 P Q N A B X D b c h))) (@finite_arrow_tail_rest (Functor_cat K C) (@OneCatNativeExactArrowPair K
  C (@additive_preadditive C Prod t Add) C1 t (@additive_terminal_object C Prod t Add) T0 P Q N) (succ (succ
  zero)) (@kernel_adjunction_family_func K C (@additive_preadditive C Prod t Add) t (@additive_terminal_object C
  Prod t Add) P (@transf_arrow_diagram_func K C B X b)) (@finite_arrow_tail_next (Functor_cat K C)
  (@OneCatNativeExactArrowPair K C (@additive_preadditive C Prod t Add) C1 t (@additive_terminal_object C Prod t
  Add) T0 P Q N) (succ (succ (succ zero))) (@kernel_adjunction_family_func K C (@additive_preadditive C Prod t
  Add) t (@additive_terminal_object C Prod t Add) P (@one_cat_native_snake_alpha_diagram K C
  (@additive_preadditive C Prod t Add) C1 t (@additive_terminal_object C Prod t Add) T0 P A B X D b c h))
  (@kernel_adjunction_family_func K C (@additive_preadditive C Prod t Add) t (@additive_terminal_object C Prod t
  Add) P (@transf_arrow_diagram_func K C B X b)) (@one_cat_native_snake_kernel_first K C (@additive_preadditive
  C Prod t Add) C1 t (@additive_terminal_object C Prod t Add) T0 P Q A B X D b c h)
  (@one_cat_native_snake_six_term_result K C C1 Prod t Add T0 P Q N A B X D b c h)) (@finite_arrow_tail_arrow
  (Functor_cat K C) (@OneCatNativeExactArrowPair K C (@additive_preadditive C Prod t Add) C1 t
  (@additive_terminal_object C Prod t Add) T0 P Q N) (succ (succ (succ zero))) (@kernel_adjunction_family_func K
  C (@additive_preadditive C Prod t Add) t (@additive_terminal_object C Prod t Add) P
  (@one_cat_native_snake_alpha_diagram K C (@additive_preadditive C Prod t Add) C1 t (@additive_terminal_object
  C Prod t Add) T0 P A B X D b c h)) (@kernel_adjunction_family_func K C (@additive_preadditive C Prod t Add) t
  (@additive_terminal_object C Prod t Add) P (@transf_arrow_diagram_func K C B X b))
  (@one_cat_native_snake_kernel_first K C (@additive_preadditive C Prod t Add) C1 t (@additive_terminal_object C
  Prod t Add) T0 P Q A B X D b c h) (@one_cat_native_snake_six_term_result K C C1 Prod t Add T0 P Q N A B X D b
  c h)) (@finite_arrow_tail_rest (Functor_cat K C) (@OneCatNativeExactArrowPair K C (@additive_preadditive C
  Prod t Add) C1 t (@additive_terminal_object C Prod t Add) T0 P Q N) (succ (succ (succ zero)))
  (@kernel_adjunction_family_func K C (@additive_preadditive C Prod t Add) t (@additive_terminal_object C Prod t
  Add) P (@one_cat_native_snake_alpha_diagram K C (@additive_preadditive C Prod t Add) C1 t
  (@additive_terminal_object C Prod t Add) T0 P A B X D b c h)) (@kernel_adjunction_family_func K C
  (@additive_preadditive C Prod t Add) t (@additive_terminal_object C Prod t Add) P (@transf_arrow_diagram_func
  K C B X b)) (@one_cat_native_snake_kernel_first K C (@additive_preadditive C Prod t Add) C1 t
  (@additive_terminal_object C Prod t Add) T0 P Q A B X D b c h) (@one_cat_native_snake_six_term_result K C C1
  Prod t Add T0 P Q N A B X D b c h)))) (@finite_arrow_tail_arrow (Functor_cat K C) (@OneCatNativeExactArrowPair
  K C (@additive_preadditive C Prod t Add) C1 t (@additive_terminal_object C Prod t Add) T0 P Q N) (succ zero)
  (@finite_arrow_tail_next (Functor_cat K C) (@OneCatNativeExactArrowPair K C (@additive_preadditive C Prod t
  Add) C1 t (@additive_terminal_object C Prod t Add) T0 P Q N) (succ (succ (succ zero)))
  (@kernel_adjunction_family_func K C (@additive_preadditive C Prod t Add) t (@additive_terminal_object C Prod t
  Add) P (@one_cat_native_snake_alpha_diagram K C (@additive_preadditive C Prod t Add) C1 t
  (@additive_terminal_object C Prod t Add) T0 P A B X D b c h)) (@kernel_adjunction_family_func K C
  (@additive_preadditive C Prod t Add) t (@additive_terminal_object C Prod t Add) P (@transf_arrow_diagram_func
  K C B X b)) (@one_cat_native_snake_kernel_first K C (@additive_preadditive C Prod t Add) C1 t
  (@additive_terminal_object C Prod t Add) T0 P Q A B X D b c h) (@one_cat_native_snake_six_term_result K C C1
  Prod t Add T0 P Q N A B X D b c h)) (@finite_arrow_tail_next (Functor_cat K C) (@OneCatNativeExactArrowPair K
  C (@additive_preadditive C Prod t Add) C1 t (@additive_terminal_object C Prod t Add) T0 P Q N) (succ (succ
  zero)) (@kernel_adjunction_family_func K C (@additive_preadditive C Prod t Add) t (@additive_terminal_object C
  Prod t Add) P (@transf_arrow_diagram_func K C B X b)) (@finite_arrow_tail_next (Functor_cat K C)
  (@OneCatNativeExactArrowPair K C (@additive_preadditive C Prod t Add) C1 t (@additive_terminal_object C Prod t
  Add) T0 P Q N) (succ (succ (succ zero))) (@kernel_adjunction_family_func K C (@additive_preadditive C Prod t
  Add) t (@additive_terminal_object C Prod t Add) P (@one_cat_native_snake_alpha_diagram K C
  (@additive_preadditive C Prod t Add) C1 t (@additive_terminal_object C Prod t Add) T0 P A B X D b c h))
  (@kernel_adjunction_family_func K C (@additive_preadditive C Prod t Add) t (@additive_terminal_object C Prod t
  Add) P (@transf_arrow_diagram_func K C B X b)) (@one_cat_native_snake_kernel_first K C (@additive_preadditive
  C Prod t Add) C1 t (@additive_terminal_object C Prod t Add) T0 P Q A B X D b c h)
  (@one_cat_native_snake_six_term_result K C C1 Prod t Add T0 P Q N A B X D b c h)) (@finite_arrow_tail_arrow
  (Functor_cat K C) (@OneCatNativeExactArrowPair K C (@additive_preadditive C Prod t Add) C1 t
  (@additive_terminal_object C Prod t Add) T0 P Q N) (succ (succ (succ zero))) (@kernel_adjunction_family_func K
  C (@additive_preadditive C Prod t Add) t (@additive_terminal_object C Prod t Add) P
  (@one_cat_native_snake_alpha_diagram K C (@additive_preadditive C Prod t Add) C1 t (@additive_terminal_object
  C Prod t Add) T0 P A B X D b c h)) (@kernel_adjunction_family_func K C (@additive_preadditive C Prod t Add) t
  (@additive_terminal_object C Prod t Add) P (@transf_arrow_diagram_func K C B X b))
  (@one_cat_native_snake_kernel_first K C (@additive_preadditive C Prod t Add) C1 t (@additive_terminal_object C
  Prod t Add) T0 P Q A B X D b c h) (@one_cat_native_snake_six_term_result K C C1 Prod t Add T0 P Q N A B X D b
  c h)) (@finite_arrow_tail_rest (Functor_cat K C) (@OneCatNativeExactArrowPair K C (@additive_preadditive C
  Prod t Add) C1 t (@additive_terminal_object C Prod t Add) T0 P Q N) (succ (succ (succ zero)))
  (@kernel_adjunction_family_func K C (@additive_preadditive C Prod t Add) t (@additive_terminal_object C Prod t
  Add) P (@one_cat_native_snake_alpha_diagram K C (@additive_preadditive C Prod t Add) C1 t
  (@additive_terminal_object C Prod t Add) T0 P A B X D b c h)) (@kernel_adjunction_family_func K C
  (@additive_preadditive C Prod t Add) t (@additive_terminal_object C Prod t Add) P (@transf_arrow_diagram_func
  K C B X b)) (@one_cat_native_snake_kernel_first K C (@additive_preadditive C Prod t Add) C1 t
  (@additive_terminal_object C Prod t Add) T0 P Q A B X D b c h) (@one_cat_native_snake_six_term_result K C C1
  Prod t Add T0 P Q N A B X D b c h))) (@finite_arrow_tail_arrow (Functor_cat K C) (@OneCatNativeExactArrowPair
  K C (@additive_preadditive C Prod t Add) C1 t (@additive_terminal_object C Prod t Add) T0 P Q N) (succ (succ
  zero)) (@kernel_adjunction_family_func K C (@additive_preadditive C Prod t Add) t (@additive_terminal_object C
  Prod t Add) P (@transf_arrow_diagram_func K C B X b)) (@finite_arrow_tail_next (Functor_cat K C)
  (@OneCatNativeExactArrowPair K C (@additive_preadditive C Prod t Add) C1 t (@additive_terminal_object C Prod t
  Add) T0 P Q N) (succ (succ (succ zero))) (@kernel_adjunction_family_func K C (@additive_preadditive C Prod t
  Add) t (@additive_terminal_object C Prod t Add) P (@one_cat_native_snake_alpha_diagram K C
  (@additive_preadditive C Prod t Add) C1 t (@additive_terminal_object C Prod t Add) T0 P A B X D b c h))
  (@kernel_adjunction_family_func K C (@additive_preadditive C Prod t Add) t (@additive_terminal_object C Prod t
  Add) P (@transf_arrow_diagram_func K C B X b)) (@one_cat_native_snake_kernel_first K C (@additive_preadditive
  C Prod t Add) C1 t (@additive_terminal_object C Prod t Add) T0 P Q A B X D b c h)
  (@one_cat_native_snake_six_term_result K C C1 Prod t Add T0 P Q N A B X D b c h)) (@finite_arrow_tail_arrow
  (Functor_cat K C) (@OneCatNativeExactArrowPair K C (@additive_preadditive C Prod t Add) C1 t
  (@additive_terminal_object C Prod t Add) T0 P Q N) (succ (succ (succ zero))) (@kernel_adjunction_family_func K
  C (@additive_preadditive C Prod t Add) t (@additive_terminal_object C Prod t Add) P
  (@one_cat_native_snake_alpha_diagram K C (@additive_preadditive C Prod t Add) C1 t (@additive_terminal_object
  C Prod t Add) T0 P A B X D b c h)) (@kernel_adjunction_family_func K C (@additive_preadditive C Prod t Add) t
  (@additive_terminal_object C Prod t Add) P (@transf_arrow_diagram_func K C B X b))
  (@one_cat_native_snake_kernel_first K C (@additive_preadditive C Prod t Add) C1 t (@additive_terminal_object C
  Prod t Add) T0 P Q A B X D b c h) (@one_cat_native_snake_six_term_result K C C1 Prod t Add T0 P Q N A B X D b
  c h)) (@finite_arrow_tail_rest (Functor_cat K C) (@OneCatNativeExactArrowPair K C (@additive_preadditive C
  Prod t Add) C1 t (@additive_terminal_object C Prod t Add) T0 P Q N) (succ (succ (succ zero)))
  (@kernel_adjunction_family_func K C (@additive_preadditive C Prod t Add) t (@additive_terminal_object C Prod t
  Add) P (@one_cat_native_snake_alpha_diagram K C (@additive_preadditive C Prod t Add) C1 t
  (@additive_terminal_object C Prod t Add) T0 P A B X D b c h)) (@kernel_adjunction_family_func K C
  (@additive_preadditive C Prod t Add) t (@additive_terminal_object C Prod t Add) P (@transf_arrow_diagram_func
  K C B X b)) (@one_cat_native_snake_kernel_first K C (@additive_preadditive C Prod t Add) C1 t
  (@additive_terminal_object C Prod t Add) T0 P Q A B X D b c h) (@one_cat_native_snake_six_term_result K C C1
  Prod t Add T0 P Q N A B X D b c h))) (@finite_arrow_tail_rest (Functor_cat K C) (@OneCatNativeExactArrowPair K
  C (@additive_preadditive C Prod t Add) C1 t (@additive_terminal_object C Prod t Add) T0 P Q N) (succ (succ
  zero)) (@kernel_adjunction_family_func K C (@additive_preadditive C Prod t Add) t (@additive_terminal_object C
  Prod t Add) P (@transf_arrow_diagram_func K C B X b)) (@finite_arrow_tail_next (Functor_cat K C)
  (@OneCatNativeExactArrowPair K C (@additive_preadditive C Prod t Add) C1 t (@additive_terminal_object C Prod t
  Add) T0 P Q N) (succ (succ (succ zero))) (@kernel_adjunction_family_func K C (@additive_preadditive C Prod t
  Add) t (@additive_terminal_object C Prod t Add) P (@one_cat_native_snake_alpha_diagram K C
  (@additive_preadditive C Prod t Add) C1 t (@additive_terminal_object C Prod t Add) T0 P A B X D b c h))
  (@kernel_adjunction_family_func K C (@additive_preadditive C Prod t Add) t (@additive_terminal_object C Prod t
  Add) P (@transf_arrow_diagram_func K C B X b)) (@one_cat_native_snake_kernel_first K C (@additive_preadditive
  C Prod t Add) C1 t (@additive_terminal_object C Prod t Add) T0 P Q A B X D b c h)
  (@one_cat_native_snake_six_term_result K C C1 Prod t Add T0 P Q N A B X D b c h)) (@finite_arrow_tail_arrow
  (Functor_cat K C) (@OneCatNativeExactArrowPair K C (@additive_preadditive C Prod t Add) C1 t
  (@additive_terminal_object C Prod t Add) T0 P Q N) (succ (succ (succ zero))) (@kernel_adjunction_family_func K
  C (@additive_preadditive C Prod t Add) t (@additive_terminal_object C Prod t Add) P
  (@one_cat_native_snake_alpha_diagram K C (@additive_preadditive C Prod t Add) C1 t (@additive_terminal_object
  C Prod t Add) T0 P A B X D b c h)) (@kernel_adjunction_family_func K C (@additive_preadditive C Prod t Add) t
  (@additive_terminal_object C Prod t Add) P (@transf_arrow_diagram_func K C B X b))
  (@one_cat_native_snake_kernel_first K C (@additive_preadditive C Prod t Add) C1 t (@additive_terminal_object C
  Prod t Add) T0 P Q A B X D b c h) (@one_cat_native_snake_six_term_result K C C1 Prod t Add T0 P Q N A B X D b
  c h)) (@finite_arrow_tail_rest (Functor_cat K C) (@OneCatNativeExactArrowPair K C (@additive_preadditive C
  Prod t Add) C1 t (@additive_terminal_object C Prod t Add) T0 P Q N) (succ (succ (succ zero)))
  (@kernel_adjunction_family_func K C (@additive_preadditive C Prod t Add) t (@additive_terminal_object C Prod t
  Add) P (@one_cat_native_snake_alpha_diagram K C (@additive_preadditive C Prod t Add) C1 t
  (@additive_terminal_object C Prod t Add) T0 P A B X D b c h)) (@kernel_adjunction_family_func K C
  (@additive_preadditive C Prod t Add) t (@additive_terminal_object C Prod t Add) P (@transf_arrow_diagram_func
  K C B X b)) (@one_cat_native_snake_kernel_first K C (@additive_preadditive C Prod t Add) C1 t
  (@additive_terminal_object C Prod t Add) T0 P Q A B X D b c h) (@one_cat_native_snake_six_term_result K C C1
  Prod t Add T0 P Q N A B X D b c h)))) (@finite_arrow_tail_rest (Functor_cat K C) (@OneCatNativeExactArrowPair
  K C (@additive_preadditive C Prod t Add) C1 t (@additive_terminal_object C Prod t Add) T0 P Q N) (succ zero)
  (@finite_arrow_tail_next (Functor_cat K C) (@OneCatNativeExactArrowPair K C (@additive_preadditive C Prod t
  Add) C1 t (@additive_terminal_object C Prod t Add) T0 P Q N) (succ (succ (succ zero)))
  (@kernel_adjunction_family_func K C (@additive_preadditive C Prod t Add) t (@additive_terminal_object C Prod t
  Add) P (@one_cat_native_snake_alpha_diagram K C (@additive_preadditive C Prod t Add) C1 t
  (@additive_terminal_object C Prod t Add) T0 P A B X D b c h)) (@kernel_adjunction_family_func K C
  (@additive_preadditive C Prod t Add) t (@additive_terminal_object C Prod t Add) P (@transf_arrow_diagram_func
  K C B X b)) (@one_cat_native_snake_kernel_first K C (@additive_preadditive C Prod t Add) C1 t
  (@additive_terminal_object C Prod t Add) T0 P Q A B X D b c h) (@one_cat_native_snake_six_term_result K C C1
  Prod t Add T0 P Q N A B X D b c h)) (@finite_arrow_tail_next (Functor_cat K C) (@OneCatNativeExactArrowPair K
  C (@additive_preadditive C Prod t Add) C1 t (@additive_terminal_object C Prod t Add) T0 P Q N) (succ (succ
  zero)) (@kernel_adjunction_family_func K C (@additive_preadditive C Prod t Add) t (@additive_terminal_object C
  Prod t Add) P (@transf_arrow_diagram_func K C B X b)) (@finite_arrow_tail_next (Functor_cat K C)
  (@OneCatNativeExactArrowPair K C (@additive_preadditive C Prod t Add) C1 t (@additive_terminal_object C Prod t
  Add) T0 P Q N) (succ (succ (succ zero))) (@kernel_adjunction_family_func K C (@additive_preadditive C Prod t
  Add) t (@additive_terminal_object C Prod t Add) P (@one_cat_native_snake_alpha_diagram K C
  (@additive_preadditive C Prod t Add) C1 t (@additive_terminal_object C Prod t Add) T0 P A B X D b c h))
  (@kernel_adjunction_family_func K C (@additive_preadditive C Prod t Add) t (@additive_terminal_object C Prod t
  Add) P (@transf_arrow_diagram_func K C B X b)) (@one_cat_native_snake_kernel_first K C (@additive_preadditive
  C Prod t Add) C1 t (@additive_terminal_object C Prod t Add) T0 P Q A B X D b c h)
  (@one_cat_native_snake_six_term_result K C C1 Prod t Add T0 P Q N A B X D b c h)) (@finite_arrow_tail_arrow
  (Functor_cat K C) (@OneCatNativeExactArrowPair K C (@additive_preadditive C Prod t Add) C1 t
  (@additive_terminal_object C Prod t Add) T0 P Q N) (succ (succ (succ zero))) (@kernel_adjunction_family_func K
  C (@additive_preadditive C Prod t Add) t (@additive_terminal_object C Prod t Add) P
  (@one_cat_native_snake_alpha_diagram K C (@additive_preadditive C Prod t Add) C1 t (@additive_terminal_object
  C Prod t Add) T0 P A B X D b c h)) (@kernel_adjunction_family_func K C (@additive_preadditive C Prod t Add) t
  (@additive_terminal_object C Prod t Add) P (@transf_arrow_diagram_func K C B X b))
  (@one_cat_native_snake_kernel_first K C (@additive_preadditive C Prod t Add) C1 t (@additive_terminal_object C
  Prod t Add) T0 P Q A B X D b c h) (@one_cat_native_snake_six_term_result K C C1 Prod t Add T0 P Q N A B X D b
  c h)) (@finite_arrow_tail_rest (Functor_cat K C) (@OneCatNativeExactArrowPair K C (@additive_preadditive C
  Prod t Add) C1 t (@additive_terminal_object C Prod t Add) T0 P Q N) (succ (succ (succ zero)))
  (@kernel_adjunction_family_func K C (@additive_preadditive C Prod t Add) t (@additive_terminal_object C Prod t
  Add) P (@one_cat_native_snake_alpha_diagram K C (@additive_preadditive C Prod t Add) C1 t
  (@additive_terminal_object C Prod t Add) T0 P A B X D b c h)) (@kernel_adjunction_family_func K C
  (@additive_preadditive C Prod t Add) t (@additive_terminal_object C Prod t Add) P (@transf_arrow_diagram_func
  K C B X b)) (@one_cat_native_snake_kernel_first K C (@additive_preadditive C Prod t Add) C1 t
  (@additive_terminal_object C Prod t Add) T0 P Q A B X D b c h) (@one_cat_native_snake_six_term_result K C C1
  Prod t Add T0 P Q N A B X D b c h))) (@finite_arrow_tail_arrow (Functor_cat K C) (@OneCatNativeExactArrowPair
  K C (@additive_preadditive C Prod t Add) C1 t (@additive_terminal_object C Prod t Add) T0 P Q N) (succ (succ
  zero)) (@kernel_adjunction_family_func K C (@additive_preadditive C Prod t Add) t (@additive_terminal_object C
  Prod t Add) P (@transf_arrow_diagram_func K C B X b)) (@finite_arrow_tail_next (Functor_cat K C)
  (@OneCatNativeExactArrowPair K C (@additive_preadditive C Prod t Add) C1 t (@additive_terminal_object C Prod t
  Add) T0 P Q N) (succ (succ (succ zero))) (@kernel_adjunction_family_func K C (@additive_preadditive C Prod t
  Add) t (@additive_terminal_object C Prod t Add) P (@one_cat_native_snake_alpha_diagram K C
  (@additive_preadditive C Prod t Add) C1 t (@additive_terminal_object C Prod t Add) T0 P A B X D b c h))
  (@kernel_adjunction_family_func K C (@additive_preadditive C Prod t Add) t (@additive_terminal_object C Prod t
  Add) P (@transf_arrow_diagram_func K C B X b)) (@one_cat_native_snake_kernel_first K C (@additive_preadditive
  C Prod t Add) C1 t (@additive_terminal_object C Prod t Add) T0 P Q A B X D b c h)
  (@one_cat_native_snake_six_term_result K C C1 Prod t Add T0 P Q N A B X D b c h)) (@finite_arrow_tail_arrow
  (Functor_cat K C) (@OneCatNativeExactArrowPair K C (@additive_preadditive C Prod t Add) C1 t
  (@additive_terminal_object C Prod t Add) T0 P Q N) (succ (succ (succ zero))) (@kernel_adjunction_family_func K
  C (@additive_preadditive C Prod t Add) t (@additive_terminal_object C Prod t Add) P
  (@one_cat_native_snake_alpha_diagram K C (@additive_preadditive C Prod t Add) C1 t (@additive_terminal_object
  C Prod t Add) T0 P A B X D b c h)) (@kernel_adjunction_family_func K C (@additive_preadditive C Prod t Add) t
  (@additive_terminal_object C Prod t Add) P (@transf_arrow_diagram_func K C B X b))
  (@one_cat_native_snake_kernel_first K C (@additive_preadditive C Prod t Add) C1 t (@additive_terminal_object C
  Prod t Add) T0 P Q A B X D b c h) (@one_cat_native_snake_six_term_result K C C1 Prod t Add T0 P Q N A B X D b
  c h)) (@finite_arrow_tail_rest (Functor_cat K C) (@OneCatNativeExactArrowPair K C (@additive_preadditive C
  Prod t Add) C1 t (@additive_terminal_object C Prod t Add) T0 P Q N) (succ (succ (succ zero)))
  (@kernel_adjunction_family_func K C (@additive_preadditive C Prod t Add) t (@additive_terminal_object C Prod t
  Add) P (@one_cat_native_snake_alpha_diagram K C (@additive_preadditive C Prod t Add) C1 t
  (@additive_terminal_object C Prod t Add) T0 P A B X D b c h)) (@kernel_adjunction_family_func K C
  (@additive_preadditive C Prod t Add) t (@additive_terminal_object C Prod t Add) P (@transf_arrow_diagram_func
  K C B X b)) (@one_cat_native_snake_kernel_first K C (@additive_preadditive C Prod t Add) C1 t
  (@additive_terminal_object C Prod t Add) T0 P Q A B X D b c h) (@one_cat_native_snake_six_term_result K C C1
  Prod t Add T0 P Q N A B X D b c h))) (@finite_arrow_tail_rest (Functor_cat K C) (@OneCatNativeExactArrowPair K
  C (@additive_preadditive C Prod t Add) C1 t (@additive_terminal_object C Prod t Add) T0 P Q N) (succ (succ
  zero)) (@kernel_adjunction_family_func K C (@additive_preadditive C Prod t Add) t (@additive_terminal_object C
  Prod t Add) P (@transf_arrow_diagram_func K C B X b)) (@finite_arrow_tail_next (Functor_cat K C)
  (@OneCatNativeExactArrowPair K C (@additive_preadditive C Prod t Add) C1 t (@additive_terminal_object C Prod t
  Add) T0 P Q N) (succ (succ (succ zero))) (@kernel_adjunction_family_func K C (@additive_preadditive C Prod t
  Add) t (@additive_terminal_object C Prod t Add) P (@one_cat_native_snake_alpha_diagram K C
  (@additive_preadditive C Prod t Add) C1 t (@additive_terminal_object C Prod t Add) T0 P A B X D b c h))
  (@kernel_adjunction_family_func K C (@additive_preadditive C Prod t Add) t (@additive_terminal_object C Prod t
  Add) P (@transf_arrow_diagram_func K C B X b)) (@one_cat_native_snake_kernel_first K C (@additive_preadditive
  C Prod t Add) C1 t (@additive_terminal_object C Prod t Add) T0 P Q A B X D b c h)
  (@one_cat_native_snake_six_term_result K C C1 Prod t Add T0 P Q N A B X D b c h)) (@finite_arrow_tail_arrow
  (Functor_cat K C) (@OneCatNativeExactArrowPair K C (@additive_preadditive C Prod t Add) C1 t
  (@additive_terminal_object C Prod t Add) T0 P Q N) (succ (succ (succ zero))) (@kernel_adjunction_family_func K
  C (@additive_preadditive C Prod t Add) t (@additive_terminal_object C Prod t Add) P
  (@one_cat_native_snake_alpha_diagram K C (@additive_preadditive C Prod t Add) C1 t (@additive_terminal_object
  C Prod t Add) T0 P A B X D b c h)) (@kernel_adjunction_family_func K C (@additive_preadditive C Prod t Add) t
  (@additive_terminal_object C Prod t Add) P (@transf_arrow_diagram_func K C B X b))
  (@one_cat_native_snake_kernel_first K C (@additive_preadditive C Prod t Add) C1 t (@additive_terminal_object C
  Prod t Add) T0 P Q A B X D b c h) (@one_cat_native_snake_six_term_result K C C1 Prod t Add T0 P Q N A B X D b
  c h)) (@finite_arrow_tail_rest (Functor_cat K C) (@OneCatNativeExactArrowPair K C (@additive_preadditive C
  Prod t Add) C1 t (@additive_terminal_object C Prod t Add) T0 P Q N) (succ (succ (succ zero)))
  (@kernel_adjunction_family_func K C (@additive_preadditive C Prod t Add) t (@additive_terminal_object C Prod t
  Add) P (@one_cat_native_snake_alpha_diagram K C (@additive_preadditive C Prod t Add) C1 t
  (@additive_terminal_object C Prod t Add) T0 P A B X D b c h)) (@kernel_adjunction_family_func K C
  (@additive_preadditive C Prod t Add) t (@additive_terminal_object C Prod t Add) P (@transf_arrow_diagram_func
  K C B X b)) (@one_cat_native_snake_kernel_first K C (@additive_preadditive C Prod t Add) C1 t
  (@additive_terminal_object C Prod t Add) T0 P Q A B X D b c h) (@one_cat_native_snake_six_term_result K C C1
  Prod t Add T0 P Q N A B X D b c h))))) (@finite_arrow_tail_arrow (Functor_cat K C)
  (@OneCatNativeExactArrowPair K C (@additive_preadditive C Prod t Add) C1 t (@additive_terminal_object C Prod t
  Add) T0 P Q N) (succ zero) (@finite_arrow_tail_next (Functor_cat K C) (@OneCatNativeExactArrowPair K C
  (@additive_preadditive C Prod t Add) C1 t (@additive_terminal_object C Prod t Add) T0 P Q N) (succ (succ (succ
  zero))) (@kernel_adjunction_family_func K C (@additive_preadditive C Prod t Add) t (@additive_terminal_object
  C Prod t Add) P (@one_cat_native_snake_alpha_diagram K C (@additive_preadditive C Prod t Add) C1 t
  (@additive_terminal_object C Prod t Add) T0 P A B X D b c h)) (@kernel_adjunction_family_func K C
  (@additive_preadditive C Prod t Add) t (@additive_terminal_object C Prod t Add) P (@transf_arrow_diagram_func
  K C B X b)) (@one_cat_native_snake_kernel_first K C (@additive_preadditive C Prod t Add) C1 t
  (@additive_terminal_object C Prod t Add) T0 P Q A B X D b c h) (@one_cat_native_snake_six_term_result K C C1
  Prod t Add T0 P Q N A B X D b c h)) (@finite_arrow_tail_next (Functor_cat K C) (@OneCatNativeExactArrowPair K
  C (@additive_preadditive C Prod t Add) C1 t (@additive_terminal_object C Prod t Add) T0 P Q N) (succ (succ
  zero)) (@kernel_adjunction_family_func K C (@additive_preadditive C Prod t Add) t (@additive_terminal_object C
  Prod t Add) P (@transf_arrow_diagram_func K C B X b)) (@finite_arrow_tail_next (Functor_cat K C)
  (@OneCatNativeExactArrowPair K C (@additive_preadditive C Prod t Add) C1 t (@additive_terminal_object C Prod t
  Add) T0 P Q N) (succ (succ (succ zero))) (@kernel_adjunction_family_func K C (@additive_preadditive C Prod t
  Add) t (@additive_terminal_object C Prod t Add) P (@one_cat_native_snake_alpha_diagram K C
  (@additive_preadditive C Prod t Add) C1 t (@additive_terminal_object C Prod t Add) T0 P A B X D b c h))
  (@kernel_adjunction_family_func K C (@additive_preadditive C Prod t Add) t (@additive_terminal_object C Prod t
  Add) P (@transf_arrow_diagram_func K C B X b)) (@one_cat_native_snake_kernel_first K C (@additive_preadditive
  C Prod t Add) C1 t (@additive_terminal_object C Prod t Add) T0 P Q A B X D b c h)
  (@one_cat_native_snake_six_term_result K C C1 Prod t Add T0 P Q N A B X D b c h)) (@finite_arrow_tail_arrow
  (Functor_cat K C) (@OneCatNativeExactArrowPair K C (@additive_preadditive C Prod t Add) C1 t
  (@additive_terminal_object C Prod t Add) T0 P Q N) (succ (succ (succ zero))) (@kernel_adjunction_family_func K
  C (@additive_preadditive C Prod t Add) t (@additive_terminal_object C Prod t Add) P
  (@one_cat_native_snake_alpha_diagram K C (@additive_preadditive C Prod t Add) C1 t (@additive_terminal_object
  C Prod t Add) T0 P A B X D b c h)) (@kernel_adjunction_family_func K C (@additive_preadditive C Prod t Add) t
  (@additive_terminal_object C Prod t Add) P (@transf_arrow_diagram_func K C B X b))
  (@one_cat_native_snake_kernel_first K C (@additive_preadditive C Prod t Add) C1 t (@additive_terminal_object C
  Prod t Add) T0 P Q A B X D b c h) (@one_cat_native_snake_six_term_result K C C1 Prod t Add T0 P Q N A B X D b
  c h)) (@finite_arrow_tail_rest (Functor_cat K C) (@OneCatNativeExactArrowPair K C (@additive_preadditive C
  Prod t Add) C1 t (@additive_terminal_object C Prod t Add) T0 P Q N) (succ (succ (succ zero)))
  (@kernel_adjunction_family_func K C (@additive_preadditive C Prod t Add) t (@additive_terminal_object C Prod t
  Add) P (@one_cat_native_snake_alpha_diagram K C (@additive_preadditive C Prod t Add) C1 t
  (@additive_terminal_object C Prod t Add) T0 P A B X D b c h)) (@kernel_adjunction_family_func K C
  (@additive_preadditive C Prod t Add) t (@additive_terminal_object C Prod t Add) P (@transf_arrow_diagram_func
  K C B X b)) (@one_cat_native_snake_kernel_first K C (@additive_preadditive C Prod t Add) C1 t
  (@additive_terminal_object C Prod t Add) T0 P Q A B X D b c h) (@one_cat_native_snake_six_term_result K C C1
  Prod t Add T0 P Q N A B X D b c h))) (@finite_arrow_tail_arrow (Functor_cat K C) (@OneCatNativeExactArrowPair
  K C (@additive_preadditive C Prod t Add) C1 t (@additive_terminal_object C Prod t Add) T0 P Q N) (succ (succ
  zero)) (@kernel_adjunction_family_func K C (@additive_preadditive C Prod t Add) t (@additive_terminal_object C
  Prod t Add) P (@transf_arrow_diagram_func K C B X b)) (@finite_arrow_tail_next (Functor_cat K C)
  (@OneCatNativeExactArrowPair K C (@additive_preadditive C Prod t Add) C1 t (@additive_terminal_object C Prod t
  Add) T0 P Q N) (succ (succ (succ zero))) (@kernel_adjunction_family_func K C (@additive_preadditive C Prod t
  Add) t (@additive_terminal_object C Prod t Add) P (@one_cat_native_snake_alpha_diagram K C
  (@additive_preadditive C Prod t Add) C1 t (@additive_terminal_object C Prod t Add) T0 P A B X D b c h))
  (@kernel_adjunction_family_func K C (@additive_preadditive C Prod t Add) t (@additive_terminal_object C Prod t
  Add) P (@transf_arrow_diagram_func K C B X b)) (@one_cat_native_snake_kernel_first K C (@additive_preadditive
  C Prod t Add) C1 t (@additive_terminal_object C Prod t Add) T0 P Q A B X D b c h)
  (@one_cat_native_snake_six_term_result K C C1 Prod t Add T0 P Q N A B X D b c h)) (@finite_arrow_tail_arrow
  (Functor_cat K C) (@OneCatNativeExactArrowPair K C (@additive_preadditive C Prod t Add) C1 t
  (@additive_terminal_object C Prod t Add) T0 P Q N) (succ (succ (succ zero))) (@kernel_adjunction_family_func K
  C (@additive_preadditive C Prod t Add) t (@additive_terminal_object C Prod t Add) P
  (@one_cat_native_snake_alpha_diagram K C (@additive_preadditive C Prod t Add) C1 t (@additive_terminal_object
  C Prod t Add) T0 P A B X D b c h)) (@kernel_adjunction_family_func K C (@additive_preadditive C Prod t Add) t
  (@additive_terminal_object C Prod t Add) P (@transf_arrow_diagram_func K C B X b))
  (@one_cat_native_snake_kernel_first K C (@additive_preadditive C Prod t Add) C1 t (@additive_terminal_object C
  Prod t Add) T0 P Q A B X D b c h) (@one_cat_native_snake_six_term_result K C C1 Prod t Add T0 P Q N A B X D b
  c h)) (@finite_arrow_tail_rest (Functor_cat K C) (@OneCatNativeExactArrowPair K C (@additive_preadditive C
  Prod t Add) C1 t (@additive_terminal_object C Prod t Add) T0 P Q N) (succ (succ (succ zero)))
  (@kernel_adjunction_family_func K C (@additive_preadditive C Prod t Add) t (@additive_terminal_object C Prod t
  Add) P (@one_cat_native_snake_alpha_diagram K C (@additive_preadditive C Prod t Add) C1 t
  (@additive_terminal_object C Prod t Add) T0 P A B X D b c h)) (@kernel_adjunction_family_func K C
  (@additive_preadditive C Prod t Add) t (@additive_terminal_object C Prod t Add) P (@transf_arrow_diagram_func
  K C B X b)) (@one_cat_native_snake_kernel_first K C (@additive_preadditive C Prod t Add) C1 t
  (@additive_terminal_object C Prod t Add) T0 P Q A B X D b c h) (@one_cat_native_snake_six_term_result K C C1
  Prod t Add T0 P Q N A B X D b c h))) (@finite_arrow_tail_rest (Functor_cat K C) (@OneCatNativeExactArrowPair K
  C (@additive_preadditive C Prod t Add) C1 t (@additive_terminal_object C Prod t Add) T0 P Q N) (succ (succ
  zero)) (@kernel_adjunction_family_func K C (@additive_preadditive C Prod t Add) t (@additive_terminal_object C
  Prod t Add) P (@transf_arrow_diagram_func K C B X b)) (@finite_arrow_tail_next (Functor_cat K C)
  (@OneCatNativeExactArrowPair K C (@additive_preadditive C Prod t Add) C1 t (@additive_terminal_object C Prod t
  Add) T0 P Q N) (succ (succ (succ zero))) (@kernel_adjunction_family_func K C (@additive_preadditive C Prod t
  Add) t (@additive_terminal_object C Prod t Add) P (@one_cat_native_snake_alpha_diagram K C
  (@additive_preadditive C Prod t Add) C1 t (@additive_terminal_object C Prod t Add) T0 P A B X D b c h))
  (@kernel_adjunction_family_func K C (@additive_preadditive C Prod t Add) t (@additive_terminal_object C Prod t
  Add) P (@transf_arrow_diagram_func K C B X b)) (@one_cat_native_snake_kernel_first K C (@additive_preadditive
  C Prod t Add) C1 t (@additive_terminal_object C Prod t Add) T0 P Q A B X D b c h)
  (@one_cat_native_snake_six_term_result K C C1 Prod t Add T0 P Q N A B X D b c h)) (@finite_arrow_tail_arrow
  (Functor_cat K C) (@OneCatNativeExactArrowPair K C (@additive_preadditive C Prod t Add) C1 t
  (@additive_terminal_object C Prod t Add) T0 P Q N) (succ (succ (succ zero))) (@kernel_adjunction_family_func K
  C (@additive_preadditive C Prod t Add) t (@additive_terminal_object C Prod t Add) P
  (@one_cat_native_snake_alpha_diagram K C (@additive_preadditive C Prod t Add) C1 t (@additive_terminal_object
  C Prod t Add) T0 P A B X D b c h)) (@kernel_adjunction_family_func K C (@additive_preadditive C Prod t Add) t
  (@additive_terminal_object C Prod t Add) P (@transf_arrow_diagram_func K C B X b))
  (@one_cat_native_snake_kernel_first K C (@additive_preadditive C Prod t Add) C1 t (@additive_terminal_object C
  Prod t Add) T0 P Q A B X D b c h) (@one_cat_native_snake_six_term_result K C C1 Prod t Add T0 P Q N A B X D b
  c h)) (@finite_arrow_tail_rest (Functor_cat K C) (@OneCatNativeExactArrowPair K C (@additive_preadditive C
  Prod t Add) C1 t (@additive_terminal_object C Prod t Add) T0 P Q N) (succ (succ (succ zero)))
  (@kernel_adjunction_family_func K C (@additive_preadditive C Prod t Add) t (@additive_terminal_object C Prod t
  Add) P (@one_cat_native_snake_alpha_diagram K C (@additive_preadditive C Prod t Add) C1 t
  (@additive_terminal_object C Prod t Add) T0 P A B X D b c h)) (@kernel_adjunction_family_func K C
  (@additive_preadditive C Prod t Add) t (@additive_terminal_object C Prod t Add) P (@transf_arrow_diagram_func
  K C B X b)) (@one_cat_native_snake_kernel_first K C (@additive_preadditive C Prod t Add) C1 t
  (@additive_terminal_object C Prod t Add) T0 P Q A B X D b c h) (@one_cat_native_snake_six_term_result K C C1
  Prod t Add T0 P Q N A B X D b c h))))) (@zero_arrow_family_zero_transf K C t (@additive_terminal_object C Prod
  t Add) T0 (@finite_arrow_tail_next (Functor_cat K C) (@OneCatNativeExactArrowPair K C (@additive_preadditive C
  Prod t Add) C1 t (@additive_terminal_object C Prod t Add) T0 P Q N) (succ (succ zero))
  (@kernel_adjunction_family_func K C (@additive_preadditive C Prod t Add) t (@additive_terminal_object C Prod t
  Add) P (@transf_arrow_diagram_func K C B X b)) (@finite_arrow_tail_next (Functor_cat K C)
  (@OneCatNativeExactArrowPair K C (@additive_preadditive C Prod t Add) C1 t (@additive_terminal_object C Prod t
  Add) T0 P Q N) (succ (succ (succ zero))) (@kernel_adjunction_family_func K C (@additive_preadditive C Prod t
  Add) t (@additive_terminal_object C Prod t Add) P (@one_cat_native_snake_alpha_diagram K C
  (@additive_preadditive C Prod t Add) C1 t (@additive_terminal_object C Prod t Add) T0 P A B X D b c h))
  (@kernel_adjunction_family_func K C (@additive_preadditive C Prod t Add) t (@additive_terminal_object C Prod t
  Add) P (@transf_arrow_diagram_func K C B X b)) (@one_cat_native_snake_kernel_first K C (@additive_preadditive
  C Prod t Add) C1 t (@additive_terminal_object C Prod t Add) T0 P Q A B X D b c h)
  (@one_cat_native_snake_six_term_result K C C1 Prod t Add T0 P Q N A B X D b c h)) (@finite_arrow_tail_arrow
  (Functor_cat K C) (@OneCatNativeExactArrowPair K C (@additive_preadditive C Prod t Add) C1 t
  (@additive_terminal_object C Prod t Add) T0 P Q N) (succ (succ (succ zero))) (@kernel_adjunction_family_func K
  C (@additive_preadditive C Prod t Add) t (@additive_terminal_object C Prod t Add) P
  (@one_cat_native_snake_alpha_diagram K C (@additive_preadditive C Prod t Add) C1 t (@additive_terminal_object
  C Prod t Add) T0 P A B X D b c h)) (@kernel_adjunction_family_func K C (@additive_preadditive C Prod t Add) t
  (@additive_terminal_object C Prod t Add) P (@transf_arrow_diagram_func K C B X b))
  (@one_cat_native_snake_kernel_first K C (@additive_preadditive C Prod t Add) C1 t (@additive_terminal_object C
  Prod t Add) T0 P Q A B X D b c h) (@one_cat_native_snake_six_term_result K C C1 Prod t Add T0 P Q N A B X D b
  c h)) (@finite_arrow_tail_rest (Functor_cat K C) (@OneCatNativeExactArrowPair K C (@additive_preadditive C
  Prod t Add) C1 t (@additive_terminal_object C Prod t Add) T0 P Q N) (succ (succ (succ zero)))
  (@kernel_adjunction_family_func K C (@additive_preadditive C Prod t Add) t (@additive_terminal_object C Prod t
  Add) P (@one_cat_native_snake_alpha_diagram K C (@additive_preadditive C Prod t Add) C1 t
  (@additive_terminal_object C Prod t Add) T0 P A B X D b c h)) (@kernel_adjunction_family_func K C
  (@additive_preadditive C Prod t Add) t (@additive_terminal_object C Prod t Add) P (@transf_arrow_diagram_func
  K C B X b)) (@one_cat_native_snake_kernel_first K C (@additive_preadditive C Prod t Add) C1 t
  (@additive_terminal_object C Prod t Add) T0 P Q A B X D b c h) (@one_cat_native_snake_six_term_result K C C1
  Prod t Add T0 P Q N A B X D b c h))) (@finite_arrow_tail_next (Functor_cat K C) (@OneCatNativeExactArrowPair K
  C (@additive_preadditive C Prod t Add) C1 t (@additive_terminal_object C Prod t Add) T0 P Q N) zero
  (@finite_arrow_tail_next (Functor_cat K C) (@OneCatNativeExactArrowPair K C (@additive_preadditive C Prod t
  Add) C1 t (@additive_terminal_object C Prod t Add) T0 P Q N) (succ (succ zero))
  (@kernel_adjunction_family_func K C (@additive_preadditive C Prod t Add) t (@additive_terminal_object C Prod t
  Add) P (@transf_arrow_diagram_func K C B X b)) (@finite_arrow_tail_next (Functor_cat K C)
  (@OneCatNativeExactArrowPair K C (@additive_preadditive C Prod t Add) C1 t (@additive_terminal_object C Prod t
  Add) T0 P Q N) (succ (succ (succ zero))) (@kernel_adjunction_family_func K C (@additive_preadditive C Prod t
  Add) t (@additive_terminal_object C Prod t Add) P (@one_cat_native_snake_alpha_diagram K C
  (@additive_preadditive C Prod t Add) C1 t (@additive_terminal_object C Prod t Add) T0 P A B X D b c h))
  (@kernel_adjunction_family_func K C (@additive_preadditive C Prod t Add) t (@additive_terminal_object C Prod t
  Add) P (@transf_arrow_diagram_func K C B X b)) (@one_cat_native_snake_kernel_first K C (@additive_preadditive
  C Prod t Add) C1 t (@additive_terminal_object C Prod t Add) T0 P Q A B X D b c h)
  (@one_cat_native_snake_six_term_result K C C1 Prod t Add T0 P Q N A B X D b c h)) (@finite_arrow_tail_arrow
  (Functor_cat K C) (@OneCatNativeExactArrowPair K C (@additive_preadditive C Prod t Add) C1 t
  (@additive_terminal_object C Prod t Add) T0 P Q N) (succ (succ (succ zero))) (@kernel_adjunction_family_func K
  C (@additive_preadditive C Prod t Add) t (@additive_terminal_object C Prod t Add) P
  (@one_cat_native_snake_alpha_diagram K C (@additive_preadditive C Prod t Add) C1 t (@additive_terminal_object
  C Prod t Add) T0 P A B X D b c h)) (@kernel_adjunction_family_func K C (@additive_preadditive C Prod t Add) t
  (@additive_terminal_object C Prod t Add) P (@transf_arrow_diagram_func K C B X b))
  (@one_cat_native_snake_kernel_first K C (@additive_preadditive C Prod t Add) C1 t (@additive_terminal_object C
  Prod t Add) T0 P Q A B X D b c h) (@one_cat_native_snake_six_term_result K C C1 Prod t Add T0 P Q N A B X D b
  c h)) (@finite_arrow_tail_rest (Functor_cat K C) (@OneCatNativeExactArrowPair K C (@additive_preadditive C
  Prod t Add) C1 t (@additive_terminal_object C Prod t Add) T0 P Q N) (succ (succ (succ zero)))
  (@kernel_adjunction_family_func K C (@additive_preadditive C Prod t Add) t (@additive_terminal_object C Prod t
  Add) P (@one_cat_native_snake_alpha_diagram K C (@additive_preadditive C Prod t Add) C1 t
  (@additive_terminal_object C Prod t Add) T0 P A B X D b c h)) (@kernel_adjunction_family_func K C
  (@additive_preadditive C Prod t Add) t (@additive_terminal_object C Prod t Add) P (@transf_arrow_diagram_func
  K C B X b)) (@one_cat_native_snake_kernel_first K C (@additive_preadditive C Prod t Add) C1 t
  (@additive_terminal_object C Prod t Add) T0 P Q A B X D b c h) (@one_cat_native_snake_six_term_result K C C1
  Prod t Add T0 P Q N A B X D b c h))) (@finite_arrow_tail_next (Functor_cat K C) (@OneCatNativeExactArrowPair K
  C (@additive_preadditive C Prod t Add) C1 t (@additive_terminal_object C Prod t Add) T0 P Q N) (succ zero)
  (@finite_arrow_tail_next (Functor_cat K C) (@OneCatNativeExactArrowPair K C (@additive_preadditive C Prod t
  Add) C1 t (@additive_terminal_object C Prod t Add) T0 P Q N) (succ (succ (succ zero)))
  (@kernel_adjunction_family_func K C (@additive_preadditive C Prod t Add) t (@additive_terminal_object C Prod t
  Add) P (@one_cat_native_snake_alpha_diagram K C (@additive_preadditive C Prod t Add) C1 t
  (@additive_terminal_object C Prod t Add) T0 P A B X D b c h)) (@kernel_adjunction_family_func K C
  (@additive_preadditive C Prod t Add) t (@additive_terminal_object C Prod t Add) P (@transf_arrow_diagram_func
  K C B X b)) (@one_cat_native_snake_kernel_first K C (@additive_preadditive C Prod t Add) C1 t
  (@additive_terminal_object C Prod t Add) T0 P Q A B X D b c h) (@one_cat_native_snake_six_term_result K C C1
  Prod t Add T0 P Q N A B X D b c h)) (@finite_arrow_tail_next (Functor_cat K C) (@OneCatNativeExactArrowPair K
  C (@additive_preadditive C Prod t Add) C1 t (@additive_terminal_object C Prod t Add) T0 P Q N) (succ (succ
  zero)) (@kernel_adjunction_family_func K C (@additive_preadditive C Prod t Add) t (@additive_terminal_object C
  Prod t Add) P (@transf_arrow_diagram_func K C B X b)) (@finite_arrow_tail_next (Functor_cat K C)
  (@OneCatNativeExactArrowPair K C (@additive_preadditive C Prod t Add) C1 t (@additive_terminal_object C Prod t
  Add) T0 P Q N) (succ (succ (succ zero))) (@kernel_adjunction_family_func K C (@additive_preadditive C Prod t
  Add) t (@additive_terminal_object C Prod t Add) P (@one_cat_native_snake_alpha_diagram K C
  (@additive_preadditive C Prod t Add) C1 t (@additive_terminal_object C Prod t Add) T0 P A B X D b c h))
  (@kernel_adjunction_family_func K C (@additive_preadditive C Prod t Add) t (@additive_terminal_object C Prod t
  Add) P (@transf_arrow_diagram_func K C B X b)) (@one_cat_native_snake_kernel_first K C (@additive_preadditive
  C Prod t Add) C1 t (@additive_terminal_object C Prod t Add) T0 P Q A B X D b c h)
  (@one_cat_native_snake_six_term_result K C C1 Prod t Add T0 P Q N A B X D b c h)) (@finite_arrow_tail_arrow
  (Functor_cat K C) (@OneCatNativeExactArrowPair K C (@additive_preadditive C Prod t Add) C1 t
  (@additive_terminal_object C Prod t Add) T0 P Q N) (succ (succ (succ zero))) (@kernel_adjunction_family_func K
  C (@additive_preadditive C Prod t Add) t (@additive_terminal_object C Prod t Add) P
  (@one_cat_native_snake_alpha_diagram K C (@additive_preadditive C Prod t Add) C1 t (@additive_terminal_object
  C Prod t Add) T0 P A B X D b c h)) (@kernel_adjunction_family_func K C (@additive_preadditive C Prod t Add) t
  (@additive_terminal_object C Prod t Add) P (@transf_arrow_diagram_func K C B X b))
  (@one_cat_native_snake_kernel_first K C (@additive_preadditive C Prod t Add) C1 t (@additive_terminal_object C
  Prod t Add) T0 P Q A B X D b c h) (@one_cat_native_snake_six_term_result K C C1 Prod t Add T0 P Q N A B X D b
  c h)) (@finite_arrow_tail_rest (Functor_cat K C) (@OneCatNativeExactArrowPair K C (@additive_preadditive C
  Prod t Add) C1 t (@additive_terminal_object C Prod t Add) T0 P Q N) (succ (succ (succ zero)))
  (@kernel_adjunction_family_func K C (@additive_preadditive C Prod t Add) t (@additive_terminal_object C Prod t
  Add) P (@one_cat_native_snake_alpha_diagram K C (@additive_preadditive C Prod t Add) C1 t
  (@additive_terminal_object C Prod t Add) T0 P A B X D b c h)) (@kernel_adjunction_family_func K C
  (@additive_preadditive C Prod t Add) t (@additive_terminal_object C Prod t Add) P (@transf_arrow_diagram_func
  K C B X b)) (@one_cat_native_snake_kernel_first K C (@additive_preadditive C Prod t Add) C1 t
  (@additive_terminal_object C Prod t Add) T0 P Q A B X D b c h) (@one_cat_native_snake_six_term_result K C C1
  Prod t Add T0 P Q N A B X D b c h))) (@finite_arrow_tail_arrow (Functor_cat K C) (@OneCatNativeExactArrowPair
  K C (@additive_preadditive C Prod t Add) C1 t (@additive_terminal_object C Prod t Add) T0 P Q N) (succ (succ
  zero)) (@kernel_adjunction_family_func K C (@additive_preadditive C Prod t Add) t (@additive_terminal_object C
  Prod t Add) P (@transf_arrow_diagram_func K C B X b)) (@finite_arrow_tail_next (Functor_cat K C)
  (@OneCatNativeExactArrowPair K C (@additive_preadditive C Prod t Add) C1 t (@additive_terminal_object C Prod t
  Add) T0 P Q N) (succ (succ (succ zero))) (@kernel_adjunction_family_func K C (@additive_preadditive C Prod t
  Add) t (@additive_terminal_object C Prod t Add) P (@one_cat_native_snake_alpha_diagram K C
  (@additive_preadditive C Prod t Add) C1 t (@additive_terminal_object C Prod t Add) T0 P A B X D b c h))
  (@kernel_adjunction_family_func K C (@additive_preadditive C Prod t Add) t (@additive_terminal_object C Prod t
  Add) P (@transf_arrow_diagram_func K C B X b)) (@one_cat_native_snake_kernel_first K C (@additive_preadditive
  C Prod t Add) C1 t (@additive_terminal_object C Prod t Add) T0 P Q A B X D b c h)
  (@one_cat_native_snake_six_term_result K C C1 Prod t Add T0 P Q N A B X D b c h)) (@finite_arrow_tail_arrow
  (Functor_cat K C) (@OneCatNativeExactArrowPair K C (@additive_preadditive C Prod t Add) C1 t
  (@additive_terminal_object C Prod t Add) T0 P Q N) (succ (succ (succ zero))) (@kernel_adjunction_family_func K
  C (@additive_preadditive C Prod t Add) t (@additive_terminal_object C Prod t Add) P
  (@one_cat_native_snake_alpha_diagram K C (@additive_preadditive C Prod t Add) C1 t (@additive_terminal_object
  C Prod t Add) T0 P A B X D b c h)) (@kernel_adjunction_family_func K C (@additive_preadditive C Prod t Add) t
  (@additive_terminal_object C Prod t Add) P (@transf_arrow_diagram_func K C B X b))
  (@one_cat_native_snake_kernel_first K C (@additive_preadditive C Prod t Add) C1 t (@additive_terminal_object C
  Prod t Add) T0 P Q A B X D b c h) (@one_cat_native_snake_six_term_result K C C1 Prod t Add T0 P Q N A B X D b
  c h)) (@finite_arrow_tail_rest (Functor_cat K C) (@OneCatNativeExactArrowPair K C (@additive_preadditive C
  Prod t Add) C1 t (@additive_terminal_object C Prod t Add) T0 P Q N) (succ (succ (succ zero)))
  (@kernel_adjunction_family_func K C (@additive_preadditive C Prod t Add) t (@additive_terminal_object C Prod t
  Add) P (@one_cat_native_snake_alpha_diagram K C (@additive_preadditive C Prod t Add) C1 t
  (@additive_terminal_object C Prod t Add) T0 P A B X D b c h)) (@kernel_adjunction_family_func K C
  (@additive_preadditive C Prod t Add) t (@additive_terminal_object C Prod t Add) P (@transf_arrow_diagram_func
  K C B X b)) (@one_cat_native_snake_kernel_first K C (@additive_preadditive C Prod t Add) C1 t
  (@additive_terminal_object C Prod t Add) T0 P Q A B X D b c h) (@one_cat_native_snake_six_term_result K C C1
  Prod t Add T0 P Q N A B X D b c h))) (@finite_arrow_tail_rest (Functor_cat K C) (@OneCatNativeExactArrowPair K
  C (@additive_preadditive C Prod t Add) C1 t (@additive_terminal_object C Prod t Add) T0 P Q N) (succ (succ
  zero)) (@kernel_adjunction_family_func K C (@additive_preadditive C Prod t Add) t (@additive_terminal_object C
  Prod t Add) P (@transf_arrow_diagram_func K C B X b)) (@finite_arrow_tail_next (Functor_cat K C)
  (@OneCatNativeExactArrowPair K C (@additive_preadditive C Prod t Add) C1 t (@additive_terminal_object C Prod t
  Add) T0 P Q N) (succ (succ (succ zero))) (@kernel_adjunction_family_func K C (@additive_preadditive C Prod t
  Add) t (@additive_terminal_object C Prod t Add) P (@one_cat_native_snake_alpha_diagram K C
  (@additive_preadditive C Prod t Add) C1 t (@additive_terminal_object C Prod t Add) T0 P A B X D b c h))
  (@kernel_adjunction_family_func K C (@additive_preadditive C Prod t Add) t (@additive_terminal_object C Prod t
  Add) P (@transf_arrow_diagram_func K C B X b)) (@one_cat_native_snake_kernel_first K C (@additive_preadditive
  C Prod t Add) C1 t (@additive_terminal_object C Prod t Add) T0 P Q A B X D b c h)
  (@one_cat_native_snake_six_term_result K C C1 Prod t Add T0 P Q N A B X D b c h)) (@finite_arrow_tail_arrow
  (Functor_cat K C) (@OneCatNativeExactArrowPair K C (@additive_preadditive C Prod t Add) C1 t
  (@additive_terminal_object C Prod t Add) T0 P Q N) (succ (succ (succ zero))) (@kernel_adjunction_family_func K
  C (@additive_preadditive C Prod t Add) t (@additive_terminal_object C Prod t Add) P
  (@one_cat_native_snake_alpha_diagram K C (@additive_preadditive C Prod t Add) C1 t (@additive_terminal_object
  C Prod t Add) T0 P A B X D b c h)) (@kernel_adjunction_family_func K C (@additive_preadditive C Prod t Add) t
  (@additive_terminal_object C Prod t Add) P (@transf_arrow_diagram_func K C B X b))
  (@one_cat_native_snake_kernel_first K C (@additive_preadditive C Prod t Add) C1 t (@additive_terminal_object C
  Prod t Add) T0 P Q A B X D b c h) (@one_cat_native_snake_six_term_result K C C1 Prod t Add T0 P Q N A B X D b
  c h)) (@finite_arrow_tail_rest (Functor_cat K C) (@OneCatNativeExactArrowPair K C (@additive_preadditive C
  Prod t Add) C1 t (@additive_terminal_object C Prod t Add) T0 P Q N) (succ (succ (succ zero)))
  (@kernel_adjunction_family_func K C (@additive_preadditive C Prod t Add) t (@additive_terminal_object C Prod t
  Add) P (@one_cat_native_snake_alpha_diagram K C (@additive_preadditive C Prod t Add) C1 t
  (@additive_terminal_object C Prod t Add) T0 P A B X D b c h)) (@kernel_adjunction_family_func K C
  (@additive_preadditive C Prod t Add) t (@additive_terminal_object C Prod t Add) P (@transf_arrow_diagram_func
  K C B X b)) (@one_cat_native_snake_kernel_first K C (@additive_preadditive C Prod t Add) C1 t
  (@additive_terminal_object C Prod t Add) T0 P Q A B X D b c h) (@one_cat_native_snake_six_term_result K C C1
  Prod t Add T0 P Q N A B X D b c h)))) (@finite_arrow_tail_arrow (Functor_cat K C) (@OneCatNativeExactArrowPair
  K C (@additive_preadditive C Prod t Add) C1 t (@additive_terminal_object C Prod t Add) T0 P Q N) (succ zero)
  (@finite_arrow_tail_next (Functor_cat K C) (@OneCatNativeExactArrowPair K C (@additive_preadditive C Prod t
  Add) C1 t (@additive_terminal_object C Prod t Add) T0 P Q N) (succ (succ (succ zero)))
  (@kernel_adjunction_family_func K C (@additive_preadditive C Prod t Add) t (@additive_terminal_object C Prod t
  Add) P (@one_cat_native_snake_alpha_diagram K C (@additive_preadditive C Prod t Add) C1 t
  (@additive_terminal_object C Prod t Add) T0 P A B X D b c h)) (@kernel_adjunction_family_func K C
  (@additive_preadditive C Prod t Add) t (@additive_terminal_object C Prod t Add) P (@transf_arrow_diagram_func
  K C B X b)) (@one_cat_native_snake_kernel_first K C (@additive_preadditive C Prod t Add) C1 t
  (@additive_terminal_object C Prod t Add) T0 P Q A B X D b c h) (@one_cat_native_snake_six_term_result K C C1
  Prod t Add T0 P Q N A B X D b c h)) (@finite_arrow_tail_next (Functor_cat K C) (@OneCatNativeExactArrowPair K
  C (@additive_preadditive C Prod t Add) C1 t (@additive_terminal_object C Prod t Add) T0 P Q N) (succ (succ
  zero)) (@kernel_adjunction_family_func K C (@additive_preadditive C Prod t Add) t (@additive_terminal_object C
  Prod t Add) P (@transf_arrow_diagram_func K C B X b)) (@finite_arrow_tail_next (Functor_cat K C)
  (@OneCatNativeExactArrowPair K C (@additive_preadditive C Prod t Add) C1 t (@additive_terminal_object C Prod t
  Add) T0 P Q N) (succ (succ (succ zero))) (@kernel_adjunction_family_func K C (@additive_preadditive C Prod t
  Add) t (@additive_terminal_object C Prod t Add) P (@one_cat_native_snake_alpha_diagram K C
  (@additive_preadditive C Prod t Add) C1 t (@additive_terminal_object C Prod t Add) T0 P A B X D b c h))
  (@kernel_adjunction_family_func K C (@additive_preadditive C Prod t Add) t (@additive_terminal_object C Prod t
  Add) P (@transf_arrow_diagram_func K C B X b)) (@one_cat_native_snake_kernel_first K C (@additive_preadditive
  C Prod t Add) C1 t (@additive_terminal_object C Prod t Add) T0 P Q A B X D b c h)
  (@one_cat_native_snake_six_term_result K C C1 Prod t Add T0 P Q N A B X D b c h)) (@finite_arrow_tail_arrow
  (Functor_cat K C) (@OneCatNativeExactArrowPair K C (@additive_preadditive C Prod t Add) C1 t
  (@additive_terminal_object C Prod t Add) T0 P Q N) (succ (succ (succ zero))) (@kernel_adjunction_family_func K
  C (@additive_preadditive C Prod t Add) t (@additive_terminal_object C Prod t Add) P
  (@one_cat_native_snake_alpha_diagram K C (@additive_preadditive C Prod t Add) C1 t (@additive_terminal_object
  C Prod t Add) T0 P A B X D b c h)) (@kernel_adjunction_family_func K C (@additive_preadditive C Prod t Add) t
  (@additive_terminal_object C Prod t Add) P (@transf_arrow_diagram_func K C B X b))
  (@one_cat_native_snake_kernel_first K C (@additive_preadditive C Prod t Add) C1 t (@additive_terminal_object C
  Prod t Add) T0 P Q A B X D b c h) (@one_cat_native_snake_six_term_result K C C1 Prod t Add T0 P Q N A B X D b
  c h)) (@finite_arrow_tail_rest (Functor_cat K C) (@OneCatNativeExactArrowPair K C (@additive_preadditive C
  Prod t Add) C1 t (@additive_terminal_object C Prod t Add) T0 P Q N) (succ (succ (succ zero)))
  (@kernel_adjunction_family_func K C (@additive_preadditive C Prod t Add) t (@additive_terminal_object C Prod t
  Add) P (@one_cat_native_snake_alpha_diagram K C (@additive_preadditive C Prod t Add) C1 t
  (@additive_terminal_object C Prod t Add) T0 P A B X D b c h)) (@kernel_adjunction_family_func K C
  (@additive_preadditive C Prod t Add) t (@additive_terminal_object C Prod t Add) P (@transf_arrow_diagram_func
  K C B X b)) (@one_cat_native_snake_kernel_first K C (@additive_preadditive C Prod t Add) C1 t
  (@additive_terminal_object C Prod t Add) T0 P Q A B X D b c h) (@one_cat_native_snake_six_term_result K C C1
  Prod t Add T0 P Q N A B X D b c h))) (@finite_arrow_tail_arrow (Functor_cat K C) (@OneCatNativeExactArrowPair
  K C (@additive_preadditive C Prod t Add) C1 t (@additive_terminal_object C Prod t Add) T0 P Q N) (succ (succ
  zero)) (@kernel_adjunction_family_func K C (@additive_preadditive C Prod t Add) t (@additive_terminal_object C
  Prod t Add) P (@transf_arrow_diagram_func K C B X b)) (@finite_arrow_tail_next (Functor_cat K C)
  (@OneCatNativeExactArrowPair K C (@additive_preadditive C Prod t Add) C1 t (@additive_terminal_object C Prod t
  Add) T0 P Q N) (succ (succ (succ zero))) (@kernel_adjunction_family_func K C (@additive_preadditive C Prod t
  Add) t (@additive_terminal_object C Prod t Add) P (@one_cat_native_snake_alpha_diagram K C
  (@additive_preadditive C Prod t Add) C1 t (@additive_terminal_object C Prod t Add) T0 P A B X D b c h))
  (@kernel_adjunction_family_func K C (@additive_preadditive C Prod t Add) t (@additive_terminal_object C Prod t
  Add) P (@transf_arrow_diagram_func K C B X b)) (@one_cat_native_snake_kernel_first K C (@additive_preadditive
  C Prod t Add) C1 t (@additive_terminal_object C Prod t Add) T0 P Q A B X D b c h)
  (@one_cat_native_snake_six_term_result K C C1 Prod t Add T0 P Q N A B X D b c h)) (@finite_arrow_tail_arrow
  (Functor_cat K C) (@OneCatNativeExactArrowPair K C (@additive_preadditive C Prod t Add) C1 t
  (@additive_terminal_object C Prod t Add) T0 P Q N) (succ (succ (succ zero))) (@kernel_adjunction_family_func K
  C (@additive_preadditive C Prod t Add) t (@additive_terminal_object C Prod t Add) P
  (@one_cat_native_snake_alpha_diagram K C (@additive_preadditive C Prod t Add) C1 t (@additive_terminal_object
  C Prod t Add) T0 P A B X D b c h)) (@kernel_adjunction_family_func K C (@additive_preadditive C Prod t Add) t
  (@additive_terminal_object C Prod t Add) P (@transf_arrow_diagram_func K C B X b))
  (@one_cat_native_snake_kernel_first K C (@additive_preadditive C Prod t Add) C1 t (@additive_terminal_object C
  Prod t Add) T0 P Q A B X D b c h) (@one_cat_native_snake_six_term_result K C C1 Prod t Add T0 P Q N A B X D b
  c h)) (@finite_arrow_tail_rest (Functor_cat K C) (@OneCatNativeExactArrowPair K C (@additive_preadditive C
  Prod t Add) C1 t (@additive_terminal_object C Prod t Add) T0 P Q N) (succ (succ (succ zero)))
  (@kernel_adjunction_family_func K C (@additive_preadditive C Prod t Add) t (@additive_terminal_object C Prod t
  Add) P (@one_cat_native_snake_alpha_diagram K C (@additive_preadditive C Prod t Add) C1 t
  (@additive_terminal_object C Prod t Add) T0 P A B X D b c h)) (@kernel_adjunction_family_func K C
  (@additive_preadditive C Prod t Add) t (@additive_terminal_object C Prod t Add) P (@transf_arrow_diagram_func
  K C B X b)) (@one_cat_native_snake_kernel_first K C (@additive_preadditive C Prod t Add) C1 t
  (@additive_terminal_object C Prod t Add) T0 P Q A B X D b c h) (@one_cat_native_snake_six_term_result K C C1
  Prod t Add T0 P Q N A B X D b c h))) (@finite_arrow_tail_rest (Functor_cat K C) (@OneCatNativeExactArrowPair K
  C (@additive_preadditive C Prod t Add) C1 t (@additive_terminal_object C Prod t Add) T0 P Q N) (succ (succ
  zero)) (@kernel_adjunction_family_func K C (@additive_preadditive C Prod t Add) t (@additive_terminal_object C
  Prod t Add) P (@transf_arrow_diagram_func K C B X b)) (@finite_arrow_tail_next (Functor_cat K C)
  (@OneCatNativeExactArrowPair K C (@additive_preadditive C Prod t Add) C1 t (@additive_terminal_object C Prod t
  Add) T0 P Q N) (succ (succ (succ zero))) (@kernel_adjunction_family_func K C (@additive_preadditive C Prod t
  Add) t (@additive_terminal_object C Prod t Add) P (@one_cat_native_snake_alpha_diagram K C
  (@additive_preadditive C Prod t Add) C1 t (@additive_terminal_object C Prod t Add) T0 P A B X D b c h))
  (@kernel_adjunction_family_func K C (@additive_preadditive C Prod t Add) t (@additive_terminal_object C Prod t
  Add) P (@transf_arrow_diagram_func K C B X b)) (@one_cat_native_snake_kernel_first K C (@additive_preadditive
  C Prod t Add) C1 t (@additive_terminal_object C Prod t Add) T0 P Q A B X D b c h)
  (@one_cat_native_snake_six_term_result K C C1 Prod t Add T0 P Q N A B X D b c h)) (@finite_arrow_tail_arrow
  (Functor_cat K C) (@OneCatNativeExactArrowPair K C (@additive_preadditive C Prod t Add) C1 t
  (@additive_terminal_object C Prod t Add) T0 P Q N) (succ (succ (succ zero))) (@kernel_adjunction_family_func K
  C (@additive_preadditive C Prod t Add) t (@additive_terminal_object C Prod t Add) P
  (@one_cat_native_snake_alpha_diagram K C (@additive_preadditive C Prod t Add) C1 t (@additive_terminal_object
  C Prod t Add) T0 P A B X D b c h)) (@kernel_adjunction_family_func K C (@additive_preadditive C Prod t Add) t
  (@additive_terminal_object C Prod t Add) P (@transf_arrow_diagram_func K C B X b))
  (@one_cat_native_snake_kernel_first K C (@additive_preadditive C Prod t Add) C1 t (@additive_terminal_object C
  Prod t Add) T0 P Q A B X D b c h) (@one_cat_native_snake_six_term_result K C C1 Prod t Add T0 P Q N A B X D b
  c h)) (@finite_arrow_tail_rest (Functor_cat K C) (@OneCatNativeExactArrowPair K C (@additive_preadditive C
  Prod t Add) C1 t (@additive_terminal_object C Prod t Add) T0 P Q N) (succ (succ (succ zero)))
  (@kernel_adjunction_family_func K C (@additive_preadditive C Prod t Add) t (@additive_terminal_object C Prod t
  Add) P (@one_cat_native_snake_alpha_diagram K C (@additive_preadditive C Prod t Add) C1 t
  (@additive_terminal_object C Prod t Add) T0 P A B X D b c h)) (@kernel_adjunction_family_func K C
  (@additive_preadditive C Prod t Add) t (@additive_terminal_object C Prod t Add) P (@transf_arrow_diagram_func
  K C B X b)) (@one_cat_native_snake_kernel_first K C (@additive_preadditive C Prod t Add) C1 t
  (@additive_terminal_object C Prod t Add) T0 P Q A B X D b c h) (@one_cat_native_snake_six_term_result K C C1
  Prod t Add T0 P Q N A B X D b c h)))) (@finite_arrow_tail_rest (Functor_cat K C) (@OneCatNativeExactArrowPair
  K C (@additive_preadditive C Prod t Add) C1 t (@additive_terminal_object C Prod t Add) T0 P Q N) (succ zero)
  (@finite_arrow_tail_next (Functor_cat K C) (@OneCatNativeExactArrowPair K C (@additive_preadditive C Prod t
  Add) C1 t (@additive_terminal_object C Prod t Add) T0 P Q N) (succ (succ (succ zero)))
  (@kernel_adjunction_family_func K C (@additive_preadditive C Prod t Add) t (@additive_terminal_object C Prod t
  Add) P (@one_cat_native_snake_alpha_diagram K C (@additive_preadditive C Prod t Add) C1 t
  (@additive_terminal_object C Prod t Add) T0 P A B X D b c h)) (@kernel_adjunction_family_func K C
  (@additive_preadditive C Prod t Add) t (@additive_terminal_object C Prod t Add) P (@transf_arrow_diagram_func
  K C B X b)) (@one_cat_native_snake_kernel_first K C (@additive_preadditive C Prod t Add) C1 t
  (@additive_terminal_object C Prod t Add) T0 P Q A B X D b c h) (@one_cat_native_snake_six_term_result K C C1
  Prod t Add T0 P Q N A B X D b c h)) (@finite_arrow_tail_next (Functor_cat K C) (@OneCatNativeExactArrowPair K
  C (@additive_preadditive C Prod t Add) C1 t (@additive_terminal_object C Prod t Add) T0 P Q N) (succ (succ
  zero)) (@kernel_adjunction_family_func K C (@additive_preadditive C Prod t Add) t (@additive_terminal_object C
  Prod t Add) P (@transf_arrow_diagram_func K C B X b)) (@finite_arrow_tail_next (Functor_cat K C)
  (@OneCatNativeExactArrowPair K C (@additive_preadditive C Prod t Add) C1 t (@additive_terminal_object C Prod t
  Add) T0 P Q N) (succ (succ (succ zero))) (@kernel_adjunction_family_func K C (@additive_preadditive C Prod t
  Add) t (@additive_terminal_object C Prod t Add) P (@one_cat_native_snake_alpha_diagram K C
  (@additive_preadditive C Prod t Add) C1 t (@additive_terminal_object C Prod t Add) T0 P A B X D b c h))
  (@kernel_adjunction_family_func K C (@additive_preadditive C Prod t Add) t (@additive_terminal_object C Prod t
  Add) P (@transf_arrow_diagram_func K C B X b)) (@one_cat_native_snake_kernel_first K C (@additive_preadditive
  C Prod t Add) C1 t (@additive_terminal_object C Prod t Add) T0 P Q A B X D b c h)
  (@one_cat_native_snake_six_term_result K C C1 Prod t Add T0 P Q N A B X D b c h)) (@finite_arrow_tail_arrow
  (Functor_cat K C) (@OneCatNativeExactArrowPair K C (@additive_preadditive C Prod t Add) C1 t
  (@additive_terminal_object C Prod t Add) T0 P Q N) (succ (succ (succ zero))) (@kernel_adjunction_family_func K
  C (@additive_preadditive C Prod t Add) t (@additive_terminal_object C Prod t Add) P
  (@one_cat_native_snake_alpha_diagram K C (@additive_preadditive C Prod t Add) C1 t (@additive_terminal_object
  C Prod t Add) T0 P A B X D b c h)) (@kernel_adjunction_family_func K C (@additive_preadditive C Prod t Add) t
  (@additive_terminal_object C Prod t Add) P (@transf_arrow_diagram_func K C B X b))
  (@one_cat_native_snake_kernel_first K C (@additive_preadditive C Prod t Add) C1 t (@additive_terminal_object C
  Prod t Add) T0 P Q A B X D b c h) (@one_cat_native_snake_six_term_result K C C1 Prod t Add T0 P Q N A B X D b
  c h)) (@finite_arrow_tail_rest (Functor_cat K C) (@OneCatNativeExactArrowPair K C (@additive_preadditive C
  Prod t Add) C1 t (@additive_terminal_object C Prod t Add) T0 P Q N) (succ (succ (succ zero)))
  (@kernel_adjunction_family_func K C (@additive_preadditive C Prod t Add) t (@additive_terminal_object C Prod t
  Add) P (@one_cat_native_snake_alpha_diagram K C (@additive_preadditive C Prod t Add) C1 t
  (@additive_terminal_object C Prod t Add) T0 P A B X D b c h)) (@kernel_adjunction_family_func K C
  (@additive_preadditive C Prod t Add) t (@additive_terminal_object C Prod t Add) P (@transf_arrow_diagram_func
  K C B X b)) (@one_cat_native_snake_kernel_first K C (@additive_preadditive C Prod t Add) C1 t
  (@additive_terminal_object C Prod t Add) T0 P Q A B X D b c h) (@one_cat_native_snake_six_term_result K C C1
  Prod t Add T0 P Q N A B X D b c h))) (@finite_arrow_tail_arrow (Functor_cat K C) (@OneCatNativeExactArrowPair
  K C (@additive_preadditive C Prod t Add) C1 t (@additive_terminal_object C Prod t Add) T0 P Q N) (succ (succ
  zero)) (@kernel_adjunction_family_func K C (@additive_preadditive C Prod t Add) t (@additive_terminal_object C
  Prod t Add) P (@transf_arrow_diagram_func K C B X b)) (@finite_arrow_tail_next (Functor_cat K C)
  (@OneCatNativeExactArrowPair K C (@additive_preadditive C Prod t Add) C1 t (@additive_terminal_object C Prod t
  Add) T0 P Q N) (succ (succ (succ zero))) (@kernel_adjunction_family_func K C (@additive_preadditive C Prod t
  Add) t (@additive_terminal_object C Prod t Add) P (@one_cat_native_snake_alpha_diagram K C
  (@additive_preadditive C Prod t Add) C1 t (@additive_terminal_object C Prod t Add) T0 P A B X D b c h))
  (@kernel_adjunction_family_func K C (@additive_preadditive C Prod t Add) t (@additive_terminal_object C Prod t
  Add) P (@transf_arrow_diagram_func K C B X b)) (@one_cat_native_snake_kernel_first K C (@additive_preadditive
  C Prod t Add) C1 t (@additive_terminal_object C Prod t Add) T0 P Q A B X D b c h)
  (@one_cat_native_snake_six_term_result K C C1 Prod t Add T0 P Q N A B X D b c h)) (@finite_arrow_tail_arrow
  (Functor_cat K C) (@OneCatNativeExactArrowPair K C (@additive_preadditive C Prod t Add) C1 t
  (@additive_terminal_object C Prod t Add) T0 P Q N) (succ (succ (succ zero))) (@kernel_adjunction_family_func K
  C (@additive_preadditive C Prod t Add) t (@additive_terminal_object C Prod t Add) P
  (@one_cat_native_snake_alpha_diagram K C (@additive_preadditive C Prod t Add) C1 t (@additive_terminal_object
  C Prod t Add) T0 P A B X D b c h)) (@kernel_adjunction_family_func K C (@additive_preadditive C Prod t Add) t
  (@additive_terminal_object C Prod t Add) P (@transf_arrow_diagram_func K C B X b))
  (@one_cat_native_snake_kernel_first K C (@additive_preadditive C Prod t Add) C1 t (@additive_terminal_object C
  Prod t Add) T0 P Q A B X D b c h) (@one_cat_native_snake_six_term_result K C C1 Prod t Add T0 P Q N A B X D b
  c h)) (@finite_arrow_tail_rest (Functor_cat K C) (@OneCatNativeExactArrowPair K C (@additive_preadditive C
  Prod t Add) C1 t (@additive_terminal_object C Prod t Add) T0 P Q N) (succ (succ (succ zero)))
  (@kernel_adjunction_family_func K C (@additive_preadditive C Prod t Add) t (@additive_terminal_object C Prod t
  Add) P (@one_cat_native_snake_alpha_diagram K C (@additive_preadditive C Prod t Add) C1 t
  (@additive_terminal_object C Prod t Add) T0 P A B X D b c h)) (@kernel_adjunction_family_func K C
  (@additive_preadditive C Prod t Add) t (@additive_terminal_object C Prod t Add) P (@transf_arrow_diagram_func
  K C B X b)) (@one_cat_native_snake_kernel_first K C (@additive_preadditive C Prod t Add) C1 t
  (@additive_terminal_object C Prod t Add) T0 P Q A B X D b c h) (@one_cat_native_snake_six_term_result K C C1
  Prod t Add T0 P Q N A B X D b c h))) (@finite_arrow_tail_rest (Functor_cat K C) (@OneCatNativeExactArrowPair K
  C (@additive_preadditive C Prod t Add) C1 t (@additive_terminal_object C Prod t Add) T0 P Q N) (succ (succ
  zero)) (@kernel_adjunction_family_func K C (@additive_preadditive C Prod t Add) t (@additive_terminal_object C
  Prod t Add) P (@transf_arrow_diagram_func K C B X b)) (@finite_arrow_tail_next (Functor_cat K C)
  (@OneCatNativeExactArrowPair K C (@additive_preadditive C Prod t Add) C1 t (@additive_terminal_object C Prod t
  Add) T0 P Q N) (succ (succ (succ zero))) (@kernel_adjunction_family_func K C (@additive_preadditive C Prod t
  Add) t (@additive_terminal_object C Prod t Add) P (@one_cat_native_snake_alpha_diagram K C
  (@additive_preadditive C Prod t Add) C1 t (@additive_terminal_object C Prod t Add) T0 P A B X D b c h))
  (@kernel_adjunction_family_func K C (@additive_preadditive C Prod t Add) t (@additive_terminal_object C Prod t
  Add) P (@transf_arrow_diagram_func K C B X b)) (@one_cat_native_snake_kernel_first K C (@additive_preadditive
  C Prod t Add) C1 t (@additive_terminal_object C Prod t Add) T0 P Q A B X D b c h)
  (@one_cat_native_snake_six_term_result K C C1 Prod t Add T0 P Q N A B X D b c h)) (@finite_arrow_tail_arrow
  (Functor_cat K C) (@OneCatNativeExactArrowPair K C (@additive_preadditive C Prod t Add) C1 t
  (@additive_terminal_object C Prod t Add) T0 P Q N) (succ (succ (succ zero))) (@kernel_adjunction_family_func K
  C (@additive_preadditive C Prod t Add) t (@additive_terminal_object C Prod t Add) P
  (@one_cat_native_snake_alpha_diagram K C (@additive_preadditive C Prod t Add) C1 t (@additive_terminal_object
  C Prod t Add) T0 P A B X D b c h)) (@kernel_adjunction_family_func K C (@additive_preadditive C Prod t Add) t
  (@additive_terminal_object C Prod t Add) P (@transf_arrow_diagram_func K C B X b))
  (@one_cat_native_snake_kernel_first K C (@additive_preadditive C Prod t Add) C1 t (@additive_terminal_object C
  Prod t Add) T0 P Q A B X D b c h) (@one_cat_native_snake_six_term_result K C C1 Prod t Add T0 P Q N A B X D b
  c h)) (@finite_arrow_tail_rest (Functor_cat K C) (@OneCatNativeExactArrowPair K C (@additive_preadditive C
  Prod t Add) C1 t (@additive_terminal_object C Prod t Add) T0 P Q N) (succ (succ (succ zero)))
  (@kernel_adjunction_family_func K C (@additive_preadditive C Prod t Add) t (@additive_terminal_object C Prod t
  Add) P (@one_cat_native_snake_alpha_diagram K C (@additive_preadditive C Prod t Add) C1 t
  (@additive_terminal_object C Prod t Add) T0 P A B X D b c h)) (@kernel_adjunction_family_func K C
  (@additive_preadditive C Prod t Add) t (@additive_terminal_object C Prod t Add) P (@transf_arrow_diagram_func
  K C B X b)) (@one_cat_native_snake_kernel_first K C (@additive_preadditive C Prod t Add) C1 t
  (@additive_terminal_object C Prod t Add) T0 P Q A B X D b c h) (@one_cat_native_snake_six_term_result K C C1
  Prod t Add T0 P Q N A B X D b c h)))))));
