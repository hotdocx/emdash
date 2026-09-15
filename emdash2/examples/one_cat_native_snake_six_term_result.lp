/* Whole native six-term result observations. */
require open emdash.emdash3_2_one_cat_native_snake_six_term_result;

// The result type fixes the original first map and its two endpoints.
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
  ⊢ (@one_cat_native_snake_six_term_result K C C1 Prod t Add T0 P Q N A B X D b c h)
  : τ (@FiniteArrowTail (Functor_cat K C) (@OneCatNativeExactArrowPair K C (@additive_preadditive C Prod t Add)
  C1 t (@additive_terminal_object C Prod t Add) T0 P Q N) (succ (succ (succ (succ zero))))
  (@kernel_adjunction_family_func K C (@additive_preadditive C Prod t Add) t (@additive_terminal_object C Prod t
  Add) P (@one_cat_native_snake_alpha_diagram K C (@additive_preadditive C Prod t Add) C1 t
  (@additive_terminal_object C Prod t Add) T0 P A B X D b c h)) (@kernel_adjunction_family_func K C
  (@additive_preadditive C Prod t Add) t (@additive_terminal_object C Prod t Add) P (@transf_arrow_diagram_func
  K C B X b)) (@one_cat_native_snake_kernel_first K C (@additive_preadditive C Prod t Add) C1 t
  (@additive_terminal_object C Prod t Add) T0 P Q A B X D b c h));

// The stored 2th map is the original whole map.
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
  ⊢ (@finite_arrow_tail_arrow (Functor_cat K C) (@OneCatNativeExactArrowPair K C (@additive_preadditive C Prod t
  Add) C1 t (@additive_terminal_object C Prod t Add) T0 P Q N) (succ (succ (succ zero)))
  (@kernel_adjunction_family_func K C (@additive_preadditive C Prod t Add) t (@additive_terminal_object C Prod t
  Add) P (@one_cat_native_snake_alpha_diagram K C (@additive_preadditive C Prod t Add) C1 t
  (@additive_terminal_object C Prod t Add) T0 P A B X D b c h)) (@kernel_adjunction_family_func K C
  (@additive_preadditive C Prod t Add) t (@additive_terminal_object C Prod t Add) P (@transf_arrow_diagram_func
  K C B X b)) (@one_cat_native_snake_kernel_first K C (@additive_preadditive C Prod t Add) C1 t
  (@additive_terminal_object C Prod t Add) T0 P Q A B X D b c h) (@one_cat_native_snake_six_term_result K C C1
  Prod t Add T0 P Q N A B X D b c h)) ≡ (@one_cat_native_snake_kernel_second K C (@additive_preadditive C Prod t
  Add) C1 t (@additive_terminal_object C Prod t Add) T0 P Q A B X D b c h);

// The stored 3th map is the original whole map.
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
  ⊢ (@finite_arrow_tail_arrow (Functor_cat K C) (@OneCatNativeExactArrowPair K C (@additive_preadditive C Prod t
  Add) C1 t (@additive_terminal_object C Prod t Add) T0 P Q N) (succ (succ zero))
  (@kernel_adjunction_family_func K C (@additive_preadditive C Prod t Add) t (@additive_terminal_object C Prod t
  Add) P (@transf_arrow_diagram_func K C B X b)) (@kernel_adjunction_family_func K C (@additive_preadditive C
  Prod t Add) t (@additive_terminal_object C Prod t Add) P (@one_cat_native_snake_gamma_diagram K C
  (@additive_preadditive C Prod t Add) C1 t (@additive_terminal_object C Prod t Add) T0 Q A B X D b c h))
  (@one_cat_native_snake_kernel_second K C (@additive_preadditive C Prod t Add) C1 t (@additive_terminal_object
  C Prod t Add) T0 P Q A B X D b c h) (@finite_arrow_tail_rest (Functor_cat K C) (@OneCatNativeExactArrowPair K
  C (@additive_preadditive C Prod t Add) C1 t (@additive_terminal_object C Prod t Add) T0 P Q N) (succ (succ
  (succ zero))) (@kernel_adjunction_family_func K C (@additive_preadditive C Prod t Add) t
  (@additive_terminal_object C Prod t Add) P (@one_cat_native_snake_alpha_diagram K C (@additive_preadditive C
  Prod t Add) C1 t (@additive_terminal_object C Prod t Add) T0 P A B X D b c h)) (@kernel_adjunction_family_func
  K C (@additive_preadditive C Prod t Add) t (@additive_terminal_object C Prod t Add) P
  (@transf_arrow_diagram_func K C B X b)) (@one_cat_native_snake_kernel_first K C (@additive_preadditive C Prod
  t Add) C1 t (@additive_terminal_object C Prod t Add) T0 P Q A B X D b c h)
  (@one_cat_native_snake_six_term_result K C C1 Prod t Add T0 P Q N A B X D b c h))) ≡
  (@one_cat_native_snake_connecting_transf K C C1 Prod t Add T0 P Q N A B X D b c h);

// The stored 4th map is the original whole map.
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
  ⊢ (@finite_arrow_tail_arrow (Functor_cat K C) (@OneCatNativeExactArrowPair K C (@additive_preadditive C Prod t
  Add) C1 t (@additive_terminal_object C Prod t Add) T0 P Q N) (succ zero) (@kernel_adjunction_family_func K C
  (@additive_preadditive C Prod t Add) t (@additive_terminal_object C Prod t Add) P
  (@one_cat_native_snake_gamma_diagram K C (@additive_preadditive C Prod t Add) C1 t (@additive_terminal_object
  C Prod t Add) T0 Q A B X D b c h)) (@cokernel_adjunction_family_func K C (@additive_preadditive C Prod t Add)
  t T0 Q (@one_cat_native_snake_alpha_diagram K C (@additive_preadditive C Prod t Add) C1 t
  (@additive_terminal_object C Prod t Add) T0 P A B X D b c h)) (@one_cat_native_snake_connecting_transf K C C1
  Prod t Add T0 P Q N A B X D b c h) (@finite_arrow_tail_rest (Functor_cat K C) (@OneCatNativeExactArrowPair K C
  (@additive_preadditive C Prod t Add) C1 t (@additive_terminal_object C Prod t Add) T0 P Q N) (succ (succ
  zero)) (@kernel_adjunction_family_func K C (@additive_preadditive C Prod t Add) t (@additive_terminal_object C
  Prod t Add) P (@transf_arrow_diagram_func K C B X b)) (@kernel_adjunction_family_func K C
  (@additive_preadditive C Prod t Add) t (@additive_terminal_object C Prod t Add) P
  (@one_cat_native_snake_gamma_diagram K C (@additive_preadditive C Prod t Add) C1 t (@additive_terminal_object
  C Prod t Add) T0 Q A B X D b c h)) (@one_cat_native_snake_kernel_second K C (@additive_preadditive C Prod t
  Add) C1 t (@additive_terminal_object C Prod t Add) T0 P Q A B X D b c h) (@finite_arrow_tail_rest (Functor_cat
  K C) (@OneCatNativeExactArrowPair K C (@additive_preadditive C Prod t Add) C1 t (@additive_terminal_object C
  Prod t Add) T0 P Q N) (succ (succ (succ zero))) (@kernel_adjunction_family_func K C (@additive_preadditive C
  Prod t Add) t (@additive_terminal_object C Prod t Add) P (@one_cat_native_snake_alpha_diagram K C
  (@additive_preadditive C Prod t Add) C1 t (@additive_terminal_object C Prod t Add) T0 P A B X D b c h))
  (@kernel_adjunction_family_func K C (@additive_preadditive C Prod t Add) t (@additive_terminal_object C Prod t
  Add) P (@transf_arrow_diagram_func K C B X b)) (@one_cat_native_snake_kernel_first K C (@additive_preadditive
  C Prod t Add) C1 t (@additive_terminal_object C Prod t Add) T0 P Q A B X D b c h)
  (@one_cat_native_snake_six_term_result K C C1 Prod t Add T0 P Q N A B X D b c h)))) ≡
  (@one_cat_native_snake_cokernel_first K C (@additive_preadditive C Prod t Add) C1 t (@additive_terminal_object
  C Prod t Add) T0 P Q A B X D b c h);

// The stored 5th map is the original whole map.
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
  ⊢ (@finite_arrow_tail_arrow (Functor_cat K C) (@OneCatNativeExactArrowPair K C (@additive_preadditive C Prod t
  Add) C1 t (@additive_terminal_object C Prod t Add) T0 P Q N) zero (@cokernel_adjunction_family_func K C
  (@additive_preadditive C Prod t Add) t T0 Q (@one_cat_native_snake_alpha_diagram K C (@additive_preadditive C
  Prod t Add) C1 t (@additive_terminal_object C Prod t Add) T0 P A B X D b c h))
  (@cokernel_adjunction_family_func K C (@additive_preadditive C Prod t Add) t T0 Q (@transf_arrow_diagram_func
  K C B X b)) (@one_cat_native_snake_cokernel_first K C (@additive_preadditive C Prod t Add) C1 t
  (@additive_terminal_object C Prod t Add) T0 P Q A B X D b c h) (@finite_arrow_tail_rest (Functor_cat K C)
  (@OneCatNativeExactArrowPair K C (@additive_preadditive C Prod t Add) C1 t (@additive_terminal_object C Prod t
  Add) T0 P Q N) (succ zero) (@kernel_adjunction_family_func K C (@additive_preadditive C Prod t Add) t
  (@additive_terminal_object C Prod t Add) P (@one_cat_native_snake_gamma_diagram K C (@additive_preadditive C
  Prod t Add) C1 t (@additive_terminal_object C Prod t Add) T0 Q A B X D b c h))
  (@cokernel_adjunction_family_func K C (@additive_preadditive C Prod t Add) t T0 Q
  (@one_cat_native_snake_alpha_diagram K C (@additive_preadditive C Prod t Add) C1 t (@additive_terminal_object
  C Prod t Add) T0 P A B X D b c h)) (@one_cat_native_snake_connecting_transf K C C1 Prod t Add T0 P Q N A B X D
  b c h) (@finite_arrow_tail_rest (Functor_cat K C) (@OneCatNativeExactArrowPair K C (@additive_preadditive C
  Prod t Add) C1 t (@additive_terminal_object C Prod t Add) T0 P Q N) (succ (succ zero))
  (@kernel_adjunction_family_func K C (@additive_preadditive C Prod t Add) t (@additive_terminal_object C Prod t
  Add) P (@transf_arrow_diagram_func K C B X b)) (@kernel_adjunction_family_func K C (@additive_preadditive C
  Prod t Add) t (@additive_terminal_object C Prod t Add) P (@one_cat_native_snake_gamma_diagram K C
  (@additive_preadditive C Prod t Add) C1 t (@additive_terminal_object C Prod t Add) T0 Q A B X D b c h))
  (@one_cat_native_snake_kernel_second K C (@additive_preadditive C Prod t Add) C1 t (@additive_terminal_object
  C Prod t Add) T0 P Q A B X D b c h) (@finite_arrow_tail_rest (Functor_cat K C) (@OneCatNativeExactArrowPair K
  C (@additive_preadditive C Prod t Add) C1 t (@additive_terminal_object C Prod t Add) T0 P Q N) (succ (succ
  (succ zero))) (@kernel_adjunction_family_func K C (@additive_preadditive C Prod t Add) t
  (@additive_terminal_object C Prod t Add) P (@one_cat_native_snake_alpha_diagram K C (@additive_preadditive C
  Prod t Add) C1 t (@additive_terminal_object C Prod t Add) T0 P A B X D b c h)) (@kernel_adjunction_family_func
  K C (@additive_preadditive C Prod t Add) t (@additive_terminal_object C Prod t Add) P
  (@transf_arrow_diagram_func K C B X b)) (@one_cat_native_snake_kernel_first K C (@additive_preadditive C Prod
  t Add) C1 t (@additive_terminal_object C Prod t Add) T0 P Q A B X D b c h)
  (@one_cat_native_snake_six_term_result K C C1 Prod t Add T0 P Q N A B X D b c h))))) ≡
  (@one_cat_native_snake_cokernel_second K C (@additive_preadditive C Prod t Add) C1 t
  (@additive_terminal_object C Prod t Add) T0 P Q A B X D b c h);

// A complete result is constructed from arbitrary a,b,c and c∘b∘a=0.
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
  (a : τ (@Transf K C A B))
  (z : τ (@= (@Transf K C A D) (@comp_fapp0 (Functor_cat K C) A X D c (@comp_fapp0 (Functor_cat K C) A B X b a))
  (@zero_arrow_family_zero_transf K C t (@additive_terminal_object C Prod t Add) T0 A D)))
  ⊢ (@one_cat_native_snake_six_term_result K C C1 Prod t Add T0 P Q N A B X D b c (@one_cat_native_snake_input K
  C C1 t (@additive_terminal_object C Prod t Add) T0 A B X D a b c z))
  : τ (@OneCatNativeSnakeSixTermResult K C C1 Prod t Add T0 P Q N A B X D b c (@one_cat_native_snake_input K C
  C1 t (@additive_terminal_object C Prod t Add) T0 A B X D a b c z));
