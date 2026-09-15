/* Whole connecting representatives retain the original K/Q and ∂. */
require open emdash.emdash3_2_one_cat_native_snake_third_representatives;

// The representative uses the original b and κ_c.
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
  ⊢ (@one_cat_native_snake_third_middle_representative_path K C C1 Prod t Add T0 P Q N A B X D b c h)
  : τ (@= (@Transf K C (@one_cat_native_snake_third_middle_cover_source K C C1 Prod t Add T0 P Q N A B X D b c
  h) X) (@comp_fapp0 (Functor_cat K C) (@one_cat_native_snake_third_middle_cover_source K C C1 Prod t Add T0 P Q
  N A B X D b c h) B X b (@one_cat_native_snake_third_middle_cover_second K C C1 Prod t Add T0 P Q N A B X D b c
  h)) (@comp_fapp0 (Functor_cat K C) (@one_cat_native_snake_third_middle_cover_source K C C1 Prod t Add T0 P Q N
  A B X D b c h) (@kernel_adjunction_family_func K C (@additive_preadditive C Prod t Add) t
  (@additive_terminal_object C Prod t Add) P (@transf_arrow_diagram_func K C X D c)) X
  (@kernel_adjunction_family_inclusion_transf K C (@additive_preadditive C Prod t Add) t
  (@additive_terminal_object C Prod t Add) P (@transf_arrow_diagram_func K C X D c)) (@comp_fapp0 (Functor_cat K
  C) (@one_cat_native_snake_third_middle_cover_source K C C1 Prod t Add T0 P Q N A B X D b c h)
  (@one_cat_native_snake_third_cover_source K C C1 Prod t Add T0 P Q N A B X D b c h)
  (@kernel_adjunction_family_func K C (@additive_preadditive C Prod t Add) t (@additive_terminal_object C Prod t
  Add) P (@transf_arrow_diagram_func K C X D c)) (@one_cat_native_snake_third_cover_lift K C C1 Prod t Add T0 P
  Q N A B X D b c h) (@one_cat_native_snake_third_middle_cover_first K C C1 Prod t Add T0 P Q N A B X D b c
  h))));

// The original ℓ sends the native E lift to the original K(c) representative.
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
  ⊢ (@one_cat_native_snake_third_left_cycle_path K C C1 Prod t Add T0 P Q N A B X D b c h)
  : τ (@= (@Transf K C (@one_cat_native_snake_third_middle_cover_source K C C1 Prod t Add T0 P Q N A B X D b c
  h) (@kernel_adjunction_family_func K C (@additive_preadditive C Prod t Add) t (@additive_terminal_object C
  Prod t Add) P (@transf_arrow_diagram_func K C X D c))) (@comp_fapp0 (Functor_cat K C)
  (@one_cat_native_snake_third_middle_cover_source K C C1 Prod t Add T0 P Q N A B X D b c h)
  (@one_cat_native_snake_cover_source K C (@additive_preadditive C Prod t Add) C1 t (@additive_terminal_object C
  Prod t Add) T0 P Q A B X D b c h) (@kernel_adjunction_family_func K C (@additive_preadditive C Prod t Add) t
  (@additive_terminal_object C Prod t Add) P (@transf_arrow_diagram_func K C X D c))
  (@one_cat_native_snake_covered_lift K C (@additive_preadditive C Prod t Add) C1 t (@additive_terminal_object C
  Prod t Add) T0 P Q A B X D b c h) (@one_cat_native_snake_third_cover_kernel_lift K C C1 Prod t Add T0 P Q N A
  B X D b c h)) (@comp_fapp0 (Functor_cat K C) (@one_cat_native_snake_third_middle_cover_source K C C1 Prod t
  Add T0 P Q N A B X D b c h) (@one_cat_native_snake_third_cover_source K C C1 Prod t Add T0 P Q N A B X D b c
  h) (@kernel_adjunction_family_func K C (@additive_preadditive C Prod t Add) t (@additive_terminal_object C
  Prod t Add) P (@transf_arrow_diagram_func K C X D c)) (@one_cat_native_snake_third_cover_lift K C C1 Prod t
  Add T0 P Q N A B X D b c h) (@one_cat_native_snake_third_middle_cover_first K C C1 Prod t Add T0 P Q N A B X D
  b c h)));

// The actual whole ∂ recovers the two original cover projections.
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
  ⊢ (@one_cat_native_snake_third_connecting_representative_path K C C1 Prod t Add T0 P Q N A B X D b c h)
  : τ (@= (@Transf K C (@one_cat_native_snake_third_middle_cover_source K C C1 Prod t Add T0 P Q N A B X D b c
  h) (@cokernel_adjunction_family_func K C (@additive_preadditive C Prod t Add) t T0 Q
  (@one_cat_native_snake_alpha_diagram K C (@additive_preadditive C Prod t Add) C1 t (@additive_terminal_object
  C Prod t Add) T0 P A B X D b c h))) (@comp_fapp0 (Functor_cat K C)
  (@one_cat_native_snake_third_middle_cover_source K C C1 Prod t Add T0 P Q N A B X D b c h)
  (@kernel_adjunction_family_func K C (@additive_preadditive C Prod t Add) t (@additive_terminal_object C Prod t
  Add) P (@one_cat_native_snake_gamma_diagram K C (@additive_preadditive C Prod t Add) C1 t
  (@additive_terminal_object C Prod t Add) T0 Q A B X D b c h)) (@cokernel_adjunction_family_func K C
  (@additive_preadditive C Prod t Add) t T0 Q (@one_cat_native_snake_alpha_diagram K C (@additive_preadditive C
  Prod t Add) C1 t (@additive_terminal_object C Prod t Add) T0 P A B X D b c h))
  (@one_cat_native_snake_connecting_transf K C C1 Prod t Add T0 P Q N A B X D b c h)
  (@one_cat_native_snake_third_connecting_representative K C C1 Prod t Add T0 P Q N A B X D b c h)) (@comp_fapp0
  (Functor_cat K C) (@one_cat_native_snake_third_middle_cover_source K C C1 Prod t Add T0 P Q N A B X D b c h)
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
  (@additive_preadditive C Prod t Add) C1 t (@additive_terminal_object C Prod t Add) T0 P Q A B X D b c h)))
  (@comp_fapp0 (Functor_cat K C) (@one_cat_native_snake_third_middle_cover_source K C C1 Prod t Add T0 P Q N A B
  X D b c h) (@one_cat_native_snake_third_cover_source K C C1 Prod t Add T0 P Q N A B X D b c h)
  (@kernel_adjunction_family_func K C (@additive_preadditive C Prod t Add) t (@additive_terminal_object C Prod t
  Add) P (@transf_arrow_diagram_func K C (@cokernel_adjunction_family_func K C (@additive_preadditive C Prod t
  Add) t T0 Q (@one_cat_native_snake_alpha_diagram K C (@additive_preadditive C Prod t Add) C1 t
  (@additive_terminal_object C Prod t Add) T0 P A B X D b c h)) (@cokernel_adjunction_family_func K C
  (@additive_preadditive C Prod t Add) t T0 Q (@transf_arrow_diagram_func K C B X b))
  (@one_cat_native_snake_cokernel_first K C (@additive_preadditive C Prod t Add) C1 t (@additive_terminal_object
  C Prod t Add) T0 P Q A B X D b c h))) (@one_cat_native_snake_third_cover_projection K C C1 Prod t Add T0 P Q N
  A B X D b c h) (@one_cat_native_snake_third_middle_cover_first K C C1 Prod t Add T0 P Q N A B X D b c h))));
