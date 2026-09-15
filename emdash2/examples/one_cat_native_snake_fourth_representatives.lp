/* Whole corrected representatives retain the original K/Q and q₁. */
require open emdash.emdash3_2_one_cat_native_snake_fourth_representatives;

// The corrected representative is killed by the original c.
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
  ⊢ (@one_cat_native_snake_fourth_difference_zero K C C1 Prod t Add T0 P Q N A B X D b c h)
  : τ (@= (@Transf K C (@one_cat_native_snake_fourth_quotient_cover_source K C C1 Prod t Add T0 P Q N A B X D b
  c h) D) (@comp_fapp0 (Functor_cat K C) (@one_cat_native_snake_fourth_quotient_cover_source K C C1 Prod t Add
  T0 P Q N A B X D b c h) X D c (@one_cat_native_snake_fourth_difference K C C1 Prod t Add T0 P Q N A B X D b c
  h)) (@zero_arrow_family_zero_transf K C t (@additive_terminal_object C Prod t Add) T0
  (@one_cat_native_snake_fourth_quotient_cover_source K C C1 Prod t Add T0 P Q N A B X D b c h) D));

// The original kernel lift reconstructs the whole difference.
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
  ⊢ (@one_cat_native_snake_fourth_kernel_reconstruction K C C1 Prod t Add T0 P Q N A B X D b c h)
  : τ (@= (@Transf K C (@one_cat_native_snake_fourth_quotient_cover_source K C C1 Prod t Add T0 P Q N A B X D b
  c h) X) (@comp_fapp0 (Functor_cat K C) (@one_cat_native_snake_fourth_quotient_cover_source K C C1 Prod t Add
  T0 P Q N A B X D b c h) (@kernel_adjunction_family_func K C (@additive_preadditive C Prod t Add) t
  (@additive_terminal_object C Prod t Add) P (@transf_arrow_diagram_func K C X D c)) X
  (@kernel_adjunction_family_inclusion_transf K C (@additive_preadditive C Prod t Add) t
  (@additive_terminal_object C Prod t Add) P (@transf_arrow_diagram_func K C X D c))
  (@one_cat_native_snake_fourth_kernel_lift K C C1 Prod t Add T0 P Q N A B X D b c h))
  (@one_cat_native_snake_fourth_difference K C C1 Prod t Add T0 P Q N A B X D b c h));

// The actual q₁ recovers the three original cover projections.
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
  ⊢ (@one_cat_native_snake_fourth_cokernel_representative_path K C C1 Prod t Add T0 P Q N A B X D b c h)
  : τ (@= (@Transf K C (@one_cat_native_snake_fourth_quotient_cover_source K C C1 Prod t Add T0 P Q N A B X D b
  c h) (@cokernel_adjunction_family_func K C (@additive_preadditive C Prod t Add) t T0 Q
  (@transf_arrow_diagram_func K C B X b))) (@comp_fapp0 (Functor_cat K C)
  (@one_cat_native_snake_fourth_quotient_cover_source K C C1 Prod t Add T0 P Q N A B X D b c h)
  (@cokernel_adjunction_family_func K C (@additive_preadditive C Prod t Add) t T0 Q
  (@one_cat_native_snake_alpha_diagram K C (@additive_preadditive C Prod t Add) C1 t (@additive_terminal_object
  C Prod t Add) T0 P A B X D b c h)) (@cokernel_adjunction_family_func K C (@additive_preadditive C Prod t Add)
  t T0 Q (@transf_arrow_diagram_func K C B X b)) (@one_cat_native_snake_cokernel_first K C
  (@additive_preadditive C Prod t Add) C1 t (@additive_terminal_object C Prod t Add) T0 P Q A B X D b c h)
  (@one_cat_native_snake_fourth_cokernel_representative K C C1 Prod t Add T0 P Q N A B X D b c h)) (@comp_fapp0
  (Functor_cat K C) (@one_cat_native_snake_fourth_quotient_cover_source K C C1 Prod t Add T0 P Q N A B X D b c
  h) (@kernel_adjunction_family_func K C (@additive_preadditive C Prod t Add) t (@additive_terminal_object C
  Prod t Add) P (@transf_arrow_diagram_func K C (@cokernel_adjunction_family_func K C (@additive_preadditive C
  Prod t Add) t T0 Q (@transf_arrow_diagram_func K C B X b)) (@cokernel_adjunction_family_func K C
  (@additive_preadditive C Prod t Add) t T0 Q (@one_cat_native_snake_gamma_diagram K C (@additive_preadditive C
  Prod t Add) C1 t (@additive_terminal_object C Prod t Add) T0 Q A B X D b c h))
  (@one_cat_native_snake_cokernel_second K C (@additive_preadditive C Prod t Add) C1 t
  (@additive_terminal_object C Prod t Add) T0 P Q A B X D b c h))) (@cokernel_adjunction_family_func K C
  (@additive_preadditive C Prod t Add) t T0 Q (@transf_arrow_diagram_func K C B X b))
  (@kernel_adjunction_family_inclusion_transf K C (@additive_preadditive C Prod t Add) t
  (@additive_terminal_object C Prod t Add) P (@transf_arrow_diagram_func K C (@cokernel_adjunction_family_func K
  C (@additive_preadditive C Prod t Add) t T0 Q (@transf_arrow_diagram_func K C B X b))
  (@cokernel_adjunction_family_func K C (@additive_preadditive C Prod t Add) t T0 Q
  (@one_cat_native_snake_gamma_diagram K C (@additive_preadditive C Prod t Add) C1 t (@additive_terminal_object
  C Prod t Add) T0 Q A B X D b c h)) (@one_cat_native_snake_cokernel_second K C (@additive_preadditive C Prod t
  Add) C1 t (@additive_terminal_object C Prod t Add) T0 P Q A B X D b c h))) (@comp_fapp0 (Functor_cat K C)
  (@one_cat_native_snake_fourth_quotient_cover_source K C C1 Prod t Add T0 P Q N A B X D b c h)
  (@one_cat_native_snake_fourth_gamma_cover_source K C C1 Prod t Add T0 P Q N A B X D b c h)
  (@kernel_adjunction_family_func K C (@additive_preadditive C Prod t Add) t (@additive_terminal_object C Prod t
  Add) P (@transf_arrow_diagram_func K C (@cokernel_adjunction_family_func K C (@additive_preadditive C Prod t
  Add) t T0 Q (@transf_arrow_diagram_func K C B X b)) (@cokernel_adjunction_family_func K C
  (@additive_preadditive C Prod t Add) t T0 Q (@one_cat_native_snake_gamma_diagram K C (@additive_preadditive C
  Prod t Add) C1 t (@additive_terminal_object C Prod t Add) T0 Q A B X D b c h))
  (@one_cat_native_snake_cokernel_second K C (@additive_preadditive C Prod t Add) C1 t
  (@additive_terminal_object C Prod t Add) T0 P Q A B X D b c h))) (@comp_fapp0 (Functor_cat K C)
  (@one_cat_native_snake_fourth_gamma_cover_source K C C1 Prod t Add T0 P Q N A B X D b c h)
  (@one_cat_native_snake_fourth_cover_source K C C1 Prod t Add T0 P Q N A B X D b c h)
  (@kernel_adjunction_family_func K C (@additive_preadditive C Prod t Add) t (@additive_terminal_object C Prod t
  Add) P (@transf_arrow_diagram_func K C (@cokernel_adjunction_family_func K C (@additive_preadditive C Prod t
  Add) t T0 Q (@transf_arrow_diagram_func K C B X b)) (@cokernel_adjunction_family_func K C
  (@additive_preadditive C Prod t Add) t T0 Q (@one_cat_native_snake_gamma_diagram K C (@additive_preadditive C
  Prod t Add) C1 t (@additive_terminal_object C Prod t Add) T0 Q A B X D b c h))
  (@one_cat_native_snake_cokernel_second K C (@additive_preadditive C Prod t Add) C1 t
  (@additive_terminal_object C Prod t Add) T0 P Q A B X D b c h)))
  (@one_cat_native_snake_fourth_cover_projection K C C1 Prod t Add T0 P Q N A B X D b c h)
  (@one_cat_native_snake_fourth_gamma_cover_first K C C1 Prod t Add T0 P Q N A B X D b c h))
  (@one_cat_native_snake_fourth_quotient_cover_first K C C1 Prod t Add T0 P Q N A B X D b c h))));
