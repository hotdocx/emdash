/* Original whole representatives and canonical first-position exactness. */
require open emdash.emdash3_2_one_cat_native_snake_first_exactness;

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
  ⊢ @one_cat_native_snake_first_comparison_covers_path K C C1 Prod t Add T0 P Q N A B X D b c h
  : τ (@= (@Transf K C (@one_cat_native_snake_first_cover_source K C (@additive_preadditive C Prod t Add) C1 t
    (@additive_terminal_object C Prod t Add) T0 P Q A B X D b c h) (@kernel_adjunction_family_func K C
    (@additive_preadditive C Prod t Add) t (@additive_terminal_object C Prod t Add) P
    (@transf_arrow_diagram_func K C (@kernel_adjunction_family_func K C (@additive_preadditive C Prod t Add) t
    (@additive_terminal_object C Prod t Add) P (@transf_arrow_diagram_func K C B X b))
    (@kernel_adjunction_family_func K C (@additive_preadditive C Prod t Add) t (@additive_terminal_object C Prod
    t Add) P (@one_cat_native_snake_gamma_diagram K C (@additive_preadditive C Prod t Add) C1 t
    (@additive_terminal_object C Prod t Add) T0 Q A B X D b c h)) (@one_cat_native_snake_kernel_second K C
    (@additive_preadditive C Prod t Add) C1 t (@additive_terminal_object C Prod t Add) T0 P Q A B X D b c h))))
    (@comp_fapp0 (Functor_cat K C) (@one_cat_native_snake_first_cover_source K C (@additive_preadditive C Prod t
    Add) C1 t (@additive_terminal_object C Prod t Add) T0 P Q A B X D b c h) (@comp_cat_fapp0 K (Functor_cat
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
    (@one_cat_native_snake_first_exact_comparison K C C1 Prod t Add T0 P Q N A B X D b c h) (@comp_fapp0
    (Functor_cat K C) (@one_cat_native_snake_first_cover_source K C (@additive_preadditive C Prod t Add) C1 t
    (@additive_terminal_object C Prod t Add) T0 P Q A B X D b c h) (@kernel_adjunction_family_func K C
    (@additive_preadditive C Prod t Add) t (@additive_terminal_object C Prod t Add) P
    (@one_cat_native_snake_alpha_diagram K C (@additive_preadditive C Prod t Add) C1 t
    (@additive_terminal_object C Prod t Add) T0 P A B X D b c h)) (@comp_cat_fapp0 K (Functor_cat
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
    (@one_cat_image_family_source_transf K C (@additive_preadditive C Prod t Add) C1 t
    (@additive_terminal_object C Prod t Add) T0 P Q (@zero_arrow_family_incoming_func K C t
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
    (@one_cat_native_snake_first_cover_to_alpha_kernel K C (@additive_preadditive C Prod t Add) C1 t
    (@additive_terminal_object C Prod t Add) T0 P Q A B X D b c h))) (@comp_fapp0 (Functor_cat K C)
    (@one_cat_native_snake_first_cover_source K C (@additive_preadditive C Prod t Add) C1 t
    (@additive_terminal_object C Prod t Add) T0 P Q A B X D b c h) (@kernel_adjunction_family_func K C
    (@additive_preadditive C Prod t Add) t (@additive_terminal_object C Prod t Add) P
    (@transf_arrow_diagram_func K C (@one_cat_native_snake_image_func K C (@additive_preadditive C Prod t Add)
    C1 t (@additive_terminal_object C Prod t Add) T0 P Q A B X D b c h) (@kernel_adjunction_family_func K C
    (@additive_preadditive C Prod t Add) t (@additive_terminal_object C Prod t Add) P
    (@transf_arrow_diagram_func K C X D c)) (@one_cat_native_snake_image_lift K C (@additive_preadditive C Prod
    t Add) C1 t (@additive_terminal_object C Prod t Add) T0 P Q A B X D b c h))) (@kernel_adjunction_family_func
    K C (@additive_preadditive C Prod t Add) t (@additive_terminal_object C Prod t Add) P
    (@transf_arrow_diagram_func K C (@kernel_adjunction_family_func K C (@additive_preadditive C Prod t Add) t
    (@additive_terminal_object C Prod t Add) P (@transf_arrow_diagram_func K C B X b))
    (@kernel_adjunction_family_func K C (@additive_preadditive C Prod t Add) t (@additive_terminal_object C Prod
    t Add) P (@one_cat_native_snake_gamma_diagram K C (@additive_preadditive C Prod t Add) C1 t
    (@additive_terminal_object C Prod t Add) T0 Q A B X D b c h)) (@one_cat_native_snake_kernel_second K C
    (@additive_preadditive C Prod t Add) C1 t (@additive_terminal_object C Prod t Add) T0 P Q A B X D b c h)))
    (@one_cat_native_snake_first_image_kernel_to_kernel K C (@additive_preadditive C Prod t Add) C1 t
    (@additive_terminal_object C Prod t Add) T0 P Q A B X D b c h) (@one_cat_native_snake_first_cover_transf K C
    (@additive_preadditive C Prod t Add) C1 t (@additive_terminal_object C Prod t Add) T0 P Q A B X D b c h)));

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
  ⊢ @one_cat_native_snake_first_comparison_cokernel_zero K C C1 Prod t Add T0 P Q N A B X D b c h
  : τ (@= (@Transf K C (@kernel_adjunction_family_func K C (@additive_preadditive C Prod t Add) t
    (@additive_terminal_object C Prod t Add) P (@transf_arrow_diagram_func K C (@kernel_adjunction_family_func K
    C (@additive_preadditive C Prod t Add) t (@additive_terminal_object C Prod t Add) P
    (@transf_arrow_diagram_func K C B X b)) (@kernel_adjunction_family_func K C (@additive_preadditive C Prod t
    Add) t (@additive_terminal_object C Prod t Add) P (@one_cat_native_snake_gamma_diagram K C
    (@additive_preadditive C Prod t Add) C1 t (@additive_terminal_object C Prod t Add) T0 Q A B X D b c h))
    (@one_cat_native_snake_kernel_second K C (@additive_preadditive C Prod t Add) C1 t
    (@additive_terminal_object C Prod t Add) T0 P Q A B X D b c h))) (@cokernel_adjunction_family_func K C
    (@additive_preadditive C Prod t Add) t T0 Q (@transf_arrow_diagram_func K C (@comp_cat_fapp0 K (Functor_cat
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
    (@one_cat_native_snake_first_exact_comparison K C C1 Prod t Add T0 P Q N A B X D b c h))))
    (@cokernel_adjunction_family_projection_transf K C (@additive_preadditive C Prod t Add) t T0 Q
    (@transf_arrow_diagram_func K C (@comp_cat_fapp0 K (Functor_cat WalkingArrow_cat C) C
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
    (@one_cat_native_snake_first_exact_comparison K C C1 Prod t Add T0 P Q N A B X D b c h)))
    (@zero_arrow_family_zero_transf K C t (@additive_terminal_object C Prod t Add) T0
    (@kernel_adjunction_family_func K C (@additive_preadditive C Prod t Add) t (@additive_terminal_object C Prod
    t Add) P (@transf_arrow_diagram_func K C (@kernel_adjunction_family_func K C (@additive_preadditive C Prod t
    Add) t (@additive_terminal_object C Prod t Add) P (@transf_arrow_diagram_func K C B X b))
    (@kernel_adjunction_family_func K C (@additive_preadditive C Prod t Add) t (@additive_terminal_object C Prod
    t Add) P (@one_cat_native_snake_gamma_diagram K C (@additive_preadditive C Prod t Add) C1 t
    (@additive_terminal_object C Prod t Add) T0 Q A B X D b c h)) (@one_cat_native_snake_kernel_second K C
    (@additive_preadditive C Prod t Add) C1 t (@additive_terminal_object C Prod t Add) T0 P Q A B X D b c h)))
    (@cokernel_adjunction_family_func K C (@additive_preadditive C Prod t Add) t T0 Q
    (@transf_arrow_diagram_func K C (@comp_cat_fapp0 K (Functor_cat WalkingArrow_cat C) C
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
    (@one_cat_native_snake_first_exact_comparison K C C1 Prod t Add T0 P Q N A B X D b c h)))));

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
  ⊢ @one_cat_native_snake_first_exact K C C1 Prod t Add T0 P Q N A B X D b c h
  : τ (@OneCatNativeSnakeFirstExactness K C C1 Prod t Add T0 P Q N A B X D b c h);

// A real consumer first forms h from arbitrary a,b,c and its whole triple-zero proof.
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
  (z : τ (@= (@Transf K C A D)
    (@comp_fapp0 (Functor_cat K C) A X D c (@comp_fapp0 (Functor_cat K C) A B X b a))
    (@zero_arrow_family_zero_transf K C t (@additive_terminal_object C Prod t Add) T0 A D)))
  ⊢ @one_cat_native_snake_first_exact K C C1 Prod t Add T0 P Q N A B X D b c (@one_cat_native_snake_input K C C1
    t (@additive_terminal_object C Prod t Add) T0 A B X D a b c z)
  : τ (@OneCatNativeSnakeFirstExactness K C C1 Prod t Add T0 P Q N A B X D b c (@one_cat_native_snake_input K C
    C1 t (@additive_terminal_object C Prod t Add) T0 A B X D a b c z));
