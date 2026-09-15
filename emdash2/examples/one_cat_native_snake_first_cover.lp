/* Original whole representatives and canonical first-position exactness. */
require open emdash.emdash3_2_one_cat_native_snake_first_cover;

assert [K C : Cat] [S : τ (@PreadditiveCategory C)]
  (C1 : τ (IsNCat (cat_succ cat_zero) C)) [t : τ (Obj C)]
  (T : τ (@TerminalObject C t)) (T0 : τ (@TerminalObject (Op_cat C) t))
  (P : τ (@KernelAdjunctionStructure C S t T)) (Q : τ (@CokernelAdjunctionStructure C S t T0))
  (N : τ (@OneCatAdjunctionNormality C S C1 t T T0 P Q))
  [A B X D : τ (Functor K C)] (b : τ (@Transf K C B X)) (c : τ (@Transf K C X D))
  (h : τ (@NativeSnakeInput K C t T A B X D b c))
  ⊢ @one_cat_native_snake_image_source_cokernel_zero K C S C1 t T T0 P Q N A B X D b c h
  : τ (@= (@Transf K C (@one_cat_native_snake_image_func K C S C1 t T T0 P Q A B X D b c h)
    (@cokernel_adjunction_family_func K C S t T0 Q (@transf_arrow_diagram_func K C A
    (@one_cat_native_snake_image_func K C S C1 t T T0 P Q A B X D b c h) (@one_cat_native_snake_source_image K C
    S C1 t T T0 P Q A B X D b c h)))) (@cokernel_adjunction_family_projection_transf K C S t T0 Q
    (@transf_arrow_diagram_func K C A (@one_cat_native_snake_image_func K C S C1 t T T0 P Q A B X D b c h)
    (@one_cat_native_snake_source_image K C S C1 t T T0 P Q A B X D b c h))) (@zero_arrow_family_zero_transf K C
    t T T0 (@one_cat_native_snake_image_func K C S C1 t T T0 P Q A B X D b c h)
    (@cokernel_adjunction_family_func K C S t T0 Q (@transf_arrow_diagram_func K C A
    (@one_cat_native_snake_image_func K C S C1 t T T0 P Q A B X D b c h) (@one_cat_native_snake_source_image K C
    S C1 t T T0 P Q A B X D b c h)))));

assert [K C : Cat] [S : τ (@PreadditiveCategory C)]
  (C1 : τ (IsNCat (cat_succ cat_zero) C)) [t : τ (Obj C)]
  (T : τ (@TerminalObject C t)) (T0 : τ (@TerminalObject (Op_cat C) t))
  (P : τ (@KernelAdjunctionStructure C S t T)) (Q : τ (@CokernelAdjunctionStructure C S t T0))
  [A B X D : τ (Functor K C)] (b : τ (@Transf K C B X)) (c : τ (@Transf K C X D))
  (h : τ (@NativeSnakeInput K C t T A B X D b c))
  ⊢ @one_cat_native_snake_first_cover_alpha_reconstruction K C S C1 t T T0 P Q A B X D b c h
  : τ (@= (@Transf K C (@one_cat_native_snake_first_cover_source K C S C1 t T T0 P Q A B X D b c h) A)
    (@comp_fapp0 (Functor_cat K C) (@one_cat_native_snake_first_cover_source K C S C1 t T T0 P Q A B X D b c h)
    (@kernel_adjunction_family_func K C S t T P (@one_cat_native_snake_alpha_diagram K C S C1 t T T0 P A B X D b
    c h)) A (@kernel_adjunction_family_inclusion_transf K C S t T P (@one_cat_native_snake_alpha_diagram K C S
    C1 t T T0 P A B X D b c h)) (@one_cat_native_snake_first_cover_to_alpha_kernel K C S C1 t T T0 P Q A B X D b
    c h)) (@one_cat_native_snake_first_cover_first K C S C1 t T T0 P Q A B X D b c h));

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
  (Y : τ (Functor K C)) (u w : τ (@Transf K C (@kernel_adjunction_family_func K C (@additive_preadditive C Prod
    t Add) t (@additive_terminal_object C Prod t Add) P (@transf_arrow_diagram_func K C
    (@one_cat_native_snake_image_func K C (@additive_preadditive C Prod t Add) C1 t (@additive_terminal_object C
    Prod t Add) T0 P Q A B X D b c h) (@kernel_adjunction_family_func K C (@additive_preadditive C Prod t Add) t
    (@additive_terminal_object C Prod t Add) P (@transf_arrow_diagram_func K C X D c))
    (@one_cat_native_snake_image_lift K C (@additive_preadditive C Prod t Add) C1 t (@additive_terminal_object C
    Prod t Add) T0 P Q A B X D b c h))) Y))
  (p : τ (@= (@Transf K C (@one_cat_native_snake_first_cover_source K C (@additive_preadditive C Prod t Add) C1
    t (@additive_terminal_object C Prod t Add) T0 P Q A B X D b c h) Y) (@comp_fapp0 (Functor_cat K C)
    (@one_cat_native_snake_first_cover_source K C (@additive_preadditive C Prod t Add) C1 t
    (@additive_terminal_object C Prod t Add) T0 P Q A B X D b c h) (@kernel_adjunction_family_func K C
    (@additive_preadditive C Prod t Add) t (@additive_terminal_object C Prod t Add) P
    (@transf_arrow_diagram_func K C (@one_cat_native_snake_image_func K C (@additive_preadditive C Prod t Add)
    C1 t (@additive_terminal_object C Prod t Add) T0 P Q A B X D b c h) (@kernel_adjunction_family_func K C
    (@additive_preadditive C Prod t Add) t (@additive_terminal_object C Prod t Add) P
    (@transf_arrow_diagram_func K C X D c)) (@one_cat_native_snake_image_lift K C (@additive_preadditive C Prod
    t Add) C1 t (@additive_terminal_object C Prod t Add) T0 P Q A B X D b c h))) Y u
    (@one_cat_native_snake_first_cover_transf K C (@additive_preadditive C Prod t Add) C1 t
    (@additive_terminal_object C Prod t Add) T0 P Q A B X D b c h)) (@comp_fapp0 (Functor_cat K C)
    (@one_cat_native_snake_first_cover_source K C (@additive_preadditive C Prod t Add) C1 t
    (@additive_terminal_object C Prod t Add) T0 P Q A B X D b c h) (@kernel_adjunction_family_func K C
    (@additive_preadditive C Prod t Add) t (@additive_terminal_object C Prod t Add) P
    (@transf_arrow_diagram_func K C (@one_cat_native_snake_image_func K C (@additive_preadditive C Prod t Add)
    C1 t (@additive_terminal_object C Prod t Add) T0 P Q A B X D b c h) (@kernel_adjunction_family_func K C
    (@additive_preadditive C Prod t Add) t (@additive_terminal_object C Prod t Add) P
    (@transf_arrow_diagram_func K C X D c)) (@one_cat_native_snake_image_lift K C (@additive_preadditive C Prod
    t Add) C1 t (@additive_terminal_object C Prod t Add) T0 P Q A B X D b c h))) Y w
    (@one_cat_native_snake_first_cover_transf K C (@additive_preadditive C Prod t Add) C1 t
    (@additive_terminal_object C Prod t Add) T0 P Q A B X D b c h))))
  ⊢ @one_cat_native_snake_first_cover_reflect_path K C C1 Prod t Add T0 P Q N A B X D b c h Y u w p
  : τ (@= (@Transf K C (@kernel_adjunction_family_func K C (@additive_preadditive C Prod t Add) t
    (@additive_terminal_object C Prod t Add) P (@transf_arrow_diagram_func K C (@one_cat_native_snake_image_func
    K C (@additive_preadditive C Prod t Add) C1 t (@additive_terminal_object C Prod t Add) T0 P Q A B X D b c h)
    (@kernel_adjunction_family_func K C (@additive_preadditive C Prod t Add) t (@additive_terminal_object C Prod
    t Add) P (@transf_arrow_diagram_func K C X D c)) (@one_cat_native_snake_image_lift K C
    (@additive_preadditive C Prod t Add) C1 t (@additive_terminal_object C Prod t Add) T0 P Q A B X D b c h)))
    Y) u w);
