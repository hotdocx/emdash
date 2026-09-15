/* Two original whole covers for exactness at Q(α). */
require open emdash.emdash3_2_one_cat_native_snake_comparison_kernels;
require open emdash.emdash3_2_one_cat_cospan_kernel_covers;

// The original whole cospan kernel L of μ:K(q₁)⇒Q(α) and π_α:K(c)⇒Q(α).
symbol one_cat_native_snake_third_cover_source [K C : Cat]
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
  : τ (Functor K C)
≔ (@one_cat_cospan_kernel_func K C C1 Prod t Add T0 P Q (@kernel_adjunction_family_func K C
  (@additive_preadditive C Prod t Add) t (@additive_terminal_object C Prod t Add) P (@transf_arrow_diagram_func
  K C (@cokernel_adjunction_family_func K C (@additive_preadditive C Prod t Add) t T0 Q
  (@one_cat_native_snake_alpha_diagram K C (@additive_preadditive C Prod t Add) C1 t (@additive_terminal_object
  C Prod t Add) T0 P A B X D b c h)) (@cokernel_adjunction_family_func K C (@additive_preadditive C Prod t Add)
  t T0 Q (@transf_arrow_diagram_func K C B X b)) (@one_cat_native_snake_cokernel_first K C
  (@additive_preadditive C Prod t Add) C1 t (@additive_terminal_object C Prod t Add) T0 P Q A B X D b c h)))
  (@kernel_adjunction_family_func K C (@additive_preadditive C Prod t Add) t (@additive_terminal_object C Prod t
  Add) P (@transf_arrow_diagram_func K C X D c)) (@cokernel_adjunction_family_func K C (@additive_preadditive C
  Prod t Add) t T0 Q (@one_cat_native_snake_alpha_diagram K C (@additive_preadditive C Prod t Add) C1 t
  (@additive_terminal_object C Prod t Add) T0 P A B X D b c h)) (@kernel_adjunction_family_inclusion_transf K C
  (@additive_preadditive C Prod t Add) t (@additive_terminal_object C Prod t Add) P (@transf_arrow_diagram_func
  K C (@cokernel_adjunction_family_func K C (@additive_preadditive C Prod t Add) t T0 Q
  (@one_cat_native_snake_alpha_diagram K C (@additive_preadditive C Prod t Add) C1 t (@additive_terminal_object
  C Prod t Add) T0 P A B X D b c h)) (@cokernel_adjunction_family_func K C (@additive_preadditive C Prod t Add)
  t T0 Q (@transf_arrow_diagram_func K C B X b)) (@one_cat_native_snake_cokernel_first K C
  (@additive_preadditive C Prod t Add) C1 t (@additive_terminal_object C Prod t Add) T0 P Q A B X D b c h)))
  (@cokernel_adjunction_family_projection_transf K C (@additive_preadditive C Prod t Add) t T0 Q
  (@one_cat_native_snake_alpha_diagram K C (@additive_preadditive C Prod t Add) C1 t (@additive_terminal_object
  C Prod t Add) T0 P A B X D b c h)));

// Its original first projection r:L⇒K(q₁).
symbol one_cat_native_snake_third_cover_projection [K C : Cat]
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
  : τ (@Transf K C (@one_cat_native_snake_third_cover_source K C C1 Prod t Add T0 P Q N A B X D b c h)
  (@kernel_adjunction_family_func K C (@additive_preadditive C Prod t Add) t (@additive_terminal_object C Prod t
  Add) P (@transf_arrow_diagram_func K C (@cokernel_adjunction_family_func K C (@additive_preadditive C Prod t
  Add) t T0 Q (@one_cat_native_snake_alpha_diagram K C (@additive_preadditive C Prod t Add) C1 t
  (@additive_terminal_object C Prod t Add) T0 P A B X D b c h)) (@cokernel_adjunction_family_func K C
  (@additive_preadditive C Prod t Add) t T0 Q (@transf_arrow_diagram_func K C B X b))
  (@one_cat_native_snake_cokernel_first K C (@additive_preadditive C Prod t Add) C1 t (@additive_terminal_object
  C Prod t Add) T0 P Q A B X D b c h))))
≔ (@one_cat_cospan_kernel_first K C C1 Prod t Add T0 P Q (@kernel_adjunction_family_func K C
  (@additive_preadditive C Prod t Add) t (@additive_terminal_object C Prod t Add) P (@transf_arrow_diagram_func
  K C (@cokernel_adjunction_family_func K C (@additive_preadditive C Prod t Add) t T0 Q
  (@one_cat_native_snake_alpha_diagram K C (@additive_preadditive C Prod t Add) C1 t (@additive_terminal_object
  C Prod t Add) T0 P A B X D b c h)) (@cokernel_adjunction_family_func K C (@additive_preadditive C Prod t Add)
  t T0 Q (@transf_arrow_diagram_func K C B X b)) (@one_cat_native_snake_cokernel_first K C
  (@additive_preadditive C Prod t Add) C1 t (@additive_terminal_object C Prod t Add) T0 P Q A B X D b c h)))
  (@kernel_adjunction_family_func K C (@additive_preadditive C Prod t Add) t (@additive_terminal_object C Prod t
  Add) P (@transf_arrow_diagram_func K C X D c)) (@cokernel_adjunction_family_func K C (@additive_preadditive C
  Prod t Add) t T0 Q (@one_cat_native_snake_alpha_diagram K C (@additive_preadditive C Prod t Add) C1 t
  (@additive_terminal_object C Prod t Add) T0 P A B X D b c h)) (@kernel_adjunction_family_inclusion_transf K C
  (@additive_preadditive C Prod t Add) t (@additive_terminal_object C Prod t Add) P (@transf_arrow_diagram_func
  K C (@cokernel_adjunction_family_func K C (@additive_preadditive C Prod t Add) t T0 Q
  (@one_cat_native_snake_alpha_diagram K C (@additive_preadditive C Prod t Add) C1 t (@additive_terminal_object
  C Prod t Add) T0 P A B X D b c h)) (@cokernel_adjunction_family_func K C (@additive_preadditive C Prod t Add)
  t T0 Q (@transf_arrow_diagram_func K C B X b)) (@one_cat_native_snake_cokernel_first K C
  (@additive_preadditive C Prod t Add) C1 t (@additive_terminal_object C Prod t Add) T0 P Q A B X D b c h)))
  (@cokernel_adjunction_family_projection_transf K C (@additive_preadditive C Prod t Add) t T0 Q
  (@one_cat_native_snake_alpha_diagram K C (@additive_preadditive C Prod t Add) C1 t (@additive_terminal_object
  C Prod t Add) T0 P A B X D b c h)));

// Its original second projection p:L⇒K(c).
symbol one_cat_native_snake_third_cover_lift [K C : Cat]
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
  : τ (@Transf K C (@one_cat_native_snake_third_cover_source K C C1 Prod t Add T0 P Q N A B X D b c h)
  (@kernel_adjunction_family_func K C (@additive_preadditive C Prod t Add) t (@additive_terminal_object C Prod t
  Add) P (@transf_arrow_diagram_func K C X D c)))
≔ (@one_cat_cospan_kernel_second K C C1 Prod t Add T0 P Q (@kernel_adjunction_family_func K C
  (@additive_preadditive C Prod t Add) t (@additive_terminal_object C Prod t Add) P (@transf_arrow_diagram_func
  K C (@cokernel_adjunction_family_func K C (@additive_preadditive C Prod t Add) t T0 Q
  (@one_cat_native_snake_alpha_diagram K C (@additive_preadditive C Prod t Add) C1 t (@additive_terminal_object
  C Prod t Add) T0 P A B X D b c h)) (@cokernel_adjunction_family_func K C (@additive_preadditive C Prod t Add)
  t T0 Q (@transf_arrow_diagram_func K C B X b)) (@one_cat_native_snake_cokernel_first K C
  (@additive_preadditive C Prod t Add) C1 t (@additive_terminal_object C Prod t Add) T0 P Q A B X D b c h)))
  (@kernel_adjunction_family_func K C (@additive_preadditive C Prod t Add) t (@additive_terminal_object C Prod t
  Add) P (@transf_arrow_diagram_func K C X D c)) (@cokernel_adjunction_family_func K C (@additive_preadditive C
  Prod t Add) t T0 Q (@one_cat_native_snake_alpha_diagram K C (@additive_preadditive C Prod t Add) C1 t
  (@additive_terminal_object C Prod t Add) T0 P A B X D b c h)) (@kernel_adjunction_family_inclusion_transf K C
  (@additive_preadditive C Prod t Add) t (@additive_terminal_object C Prod t Add) P (@transf_arrow_diagram_func
  K C (@cokernel_adjunction_family_func K C (@additive_preadditive C Prod t Add) t T0 Q
  (@one_cat_native_snake_alpha_diagram K C (@additive_preadditive C Prod t Add) C1 t (@additive_terminal_object
  C Prod t Add) T0 P A B X D b c h)) (@cokernel_adjunction_family_func K C (@additive_preadditive C Prod t Add)
  t T0 Q (@transf_arrow_diagram_func K C B X b)) (@one_cat_native_snake_cokernel_first K C
  (@additive_preadditive C Prod t Add) C1 t (@additive_terminal_object C Prod t Add) T0 P Q A B X D b c h)))
  (@cokernel_adjunction_family_projection_transf K C (@additive_preadditive C Prod t Add) t T0 Q
  (@one_cat_native_snake_alpha_diagram K C (@additive_preadditive C Prod t Add) C1 t (@additive_terminal_object
  C Prod t Add) T0 P A B X D b c h)));

// The original projections satisfy μr=π_αp wholly.
symbol one_cat_native_snake_third_cover_compatibility [K C : Cat]
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
  (@cokernel_adjunction_family_func K C (@additive_preadditive C Prod t Add) t T0 Q
  (@one_cat_native_snake_alpha_diagram K C (@additive_preadditive C Prod t Add) C1 t (@additive_terminal_object
  C Prod t Add) T0 P A B X D b c h))) (@comp_fapp0 (Functor_cat K C) (@one_cat_native_snake_third_cover_source K
  C C1 Prod t Add T0 P Q N A B X D b c h) (@kernel_adjunction_family_func K C (@additive_preadditive C Prod t
  Add) t (@additive_terminal_object C Prod t Add) P (@transf_arrow_diagram_func K C
  (@cokernel_adjunction_family_func K C (@additive_preadditive C Prod t Add) t T0 Q
  (@one_cat_native_snake_alpha_diagram K C (@additive_preadditive C Prod t Add) C1 t (@additive_terminal_object
  C Prod t Add) T0 P A B X D b c h)) (@cokernel_adjunction_family_func K C (@additive_preadditive C Prod t Add)
  t T0 Q (@transf_arrow_diagram_func K C B X b)) (@one_cat_native_snake_cokernel_first K C
  (@additive_preadditive C Prod t Add) C1 t (@additive_terminal_object C Prod t Add) T0 P Q A B X D b c h)))
  (@cokernel_adjunction_family_func K C (@additive_preadditive C Prod t Add) t T0 Q
  (@one_cat_native_snake_alpha_diagram K C (@additive_preadditive C Prod t Add) C1 t (@additive_terminal_object
  C Prod t Add) T0 P A B X D b c h)) (@kernel_adjunction_family_inclusion_transf K C (@additive_preadditive C
  Prod t Add) t (@additive_terminal_object C Prod t Add) P (@transf_arrow_diagram_func K C
  (@cokernel_adjunction_family_func K C (@additive_preadditive C Prod t Add) t T0 Q
  (@one_cat_native_snake_alpha_diagram K C (@additive_preadditive C Prod t Add) C1 t (@additive_terminal_object
  C Prod t Add) T0 P A B X D b c h)) (@cokernel_adjunction_family_func K C (@additive_preadditive C Prod t Add)
  t T0 Q (@transf_arrow_diagram_func K C B X b)) (@one_cat_native_snake_cokernel_first K C
  (@additive_preadditive C Prod t Add) C1 t (@additive_terminal_object C Prod t Add) T0 P Q A B X D b c h)))
  (@one_cat_native_snake_third_cover_projection K C C1 Prod t Add T0 P Q N A B X D b c h)) (@comp_fapp0
  (Functor_cat K C) (@one_cat_native_snake_third_cover_source K C C1 Prod t Add T0 P Q N A B X D b c h)
  (@kernel_adjunction_family_func K C (@additive_preadditive C Prod t Add) t (@additive_terminal_object C Prod t
  Add) P (@transf_arrow_diagram_func K C X D c)) (@cokernel_adjunction_family_func K C (@additive_preadditive C
  Prod t Add) t T0 Q (@one_cat_native_snake_alpha_diagram K C (@additive_preadditive C Prod t Add) C1 t
  (@additive_terminal_object C Prod t Add) T0 P A B X D b c h)) (@cokernel_adjunction_family_projection_transf K
  C (@additive_preadditive C Prod t Add) t T0 Q (@one_cat_native_snake_alpha_diagram K C (@additive_preadditive
  C Prod t Add) C1 t (@additive_terminal_object C Prod t Add) T0 P A B X D b c h))
  (@one_cat_native_snake_third_cover_lift K C C1 Prod t Add T0 P Q N A B X D b c h)))
≔ (@one_cat_cospan_kernel_compatibility K C C1 Prod t Add T0 P Q (@kernel_adjunction_family_func K C
  (@additive_preadditive C Prod t Add) t (@additive_terminal_object C Prod t Add) P (@transf_arrow_diagram_func
  K C (@cokernel_adjunction_family_func K C (@additive_preadditive C Prod t Add) t T0 Q
  (@one_cat_native_snake_alpha_diagram K C (@additive_preadditive C Prod t Add) C1 t (@additive_terminal_object
  C Prod t Add) T0 P A B X D b c h)) (@cokernel_adjunction_family_func K C (@additive_preadditive C Prod t Add)
  t T0 Q (@transf_arrow_diagram_func K C B X b)) (@one_cat_native_snake_cokernel_first K C
  (@additive_preadditive C Prod t Add) C1 t (@additive_terminal_object C Prod t Add) T0 P Q A B X D b c h)))
  (@kernel_adjunction_family_func K C (@additive_preadditive C Prod t Add) t (@additive_terminal_object C Prod t
  Add) P (@transf_arrow_diagram_func K C X D c)) (@cokernel_adjunction_family_func K C (@additive_preadditive C
  Prod t Add) t T0 Q (@one_cat_native_snake_alpha_diagram K C (@additive_preadditive C Prod t Add) C1 t
  (@additive_terminal_object C Prod t Add) T0 P A B X D b c h)) (@kernel_adjunction_family_inclusion_transf K C
  (@additive_preadditive C Prod t Add) t (@additive_terminal_object C Prod t Add) P (@transf_arrow_diagram_func
  K C (@cokernel_adjunction_family_func K C (@additive_preadditive C Prod t Add) t T0 Q
  (@one_cat_native_snake_alpha_diagram K C (@additive_preadditive C Prod t Add) C1 t (@additive_terminal_object
  C Prod t Add) T0 P A B X D b c h)) (@cokernel_adjunction_family_func K C (@additive_preadditive C Prod t Add)
  t T0 Q (@transf_arrow_diagram_func K C B X b)) (@one_cat_native_snake_cokernel_first K C
  (@additive_preadditive C Prod t Add) C1 t (@additive_terminal_object C Prod t Add) T0 P Q A B X D b c h)))
  (@cokernel_adjunction_family_projection_transf K C (@additive_preadditive C Prod t Add) t T0 Q
  (@one_cat_native_snake_alpha_diagram K C (@additive_preadditive C Prod t Add) C1 t (@additive_terminal_object
  C Prod t Add) T0 P A B X D b c h)));

// The original quotient and derived cospan cover cancel whole maps out of K(q₁).
symbol one_cat_native_snake_third_cover_reflect_path [K C : Cat]
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
  (@cokernel_adjunction_family_func K C (@additive_preadditive C Prod t Add) t T0 Q
  (@one_cat_native_snake_alpha_diagram K C (@additive_preadditive C Prod t Add) C1 t (@additive_terminal_object
  C Prod t Add) T0 P A B X D b c h)) (@cokernel_adjunction_family_func K C (@additive_preadditive C Prod t Add)
  t T0 Q (@transf_arrow_diagram_func K C B X b)) (@one_cat_native_snake_cokernel_first K C
  (@additive_preadditive C Prod t Add) C1 t (@additive_terminal_object C Prod t Add) T0 P Q A B X D b c h))) Y))
  (p : τ (@= (@Transf K C (@one_cat_native_snake_third_cover_source K C C1 Prod t Add T0 P Q N A B X D b c h) Y)
  (@comp_fapp0 (Functor_cat K C) (@one_cat_native_snake_third_cover_source K C C1 Prod t Add T0 P Q N A B X D b
  c h) (@kernel_adjunction_family_func K C (@additive_preadditive C Prod t Add) t (@additive_terminal_object C
  Prod t Add) P (@transf_arrow_diagram_func K C (@cokernel_adjunction_family_func K C (@additive_preadditive C
  Prod t Add) t T0 Q (@one_cat_native_snake_alpha_diagram K C (@additive_preadditive C Prod t Add) C1 t
  (@additive_terminal_object C Prod t Add) T0 P A B X D b c h)) (@cokernel_adjunction_family_func K C
  (@additive_preadditive C Prod t Add) t T0 Q (@transf_arrow_diagram_func K C B X b))
  (@one_cat_native_snake_cokernel_first K C (@additive_preadditive C Prod t Add) C1 t (@additive_terminal_object
  C Prod t Add) T0 P Q A B X D b c h))) Y u (@one_cat_native_snake_third_cover_projection K C C1 Prod t Add T0 P
  Q N A B X D b c h)) (@comp_fapp0 (Functor_cat K C) (@one_cat_native_snake_third_cover_source K C C1 Prod t Add
  T0 P Q N A B X D b c h) (@kernel_adjunction_family_func K C (@additive_preadditive C Prod t Add) t
  (@additive_terminal_object C Prod t Add) P (@transf_arrow_diagram_func K C (@cokernel_adjunction_family_func K
  C (@additive_preadditive C Prod t Add) t T0 Q (@one_cat_native_snake_alpha_diagram K C (@additive_preadditive
  C Prod t Add) C1 t (@additive_terminal_object C Prod t Add) T0 P A B X D b c h))
  (@cokernel_adjunction_family_func K C (@additive_preadditive C Prod t Add) t T0 Q (@transf_arrow_diagram_func
  K C B X b)) (@one_cat_native_snake_cokernel_first K C (@additive_preadditive C Prod t Add) C1 t
  (@additive_terminal_object C Prod t Add) T0 P Q A B X D b c h))) Y w
  (@one_cat_native_snake_third_cover_projection K C C1 Prod t Add T0 P Q N A B X D b c h))))
  : τ (@= (@Transf K C (@kernel_adjunction_family_func K C (@additive_preadditive C Prod t Add) t
  (@additive_terminal_object C Prod t Add) P (@transf_arrow_diagram_func K C (@cokernel_adjunction_family_func K
  C (@additive_preadditive C Prod t Add) t T0 Q (@one_cat_native_snake_alpha_diagram K C (@additive_preadditive
  C Prod t Add) C1 t (@additive_terminal_object C Prod t Add) T0 P A B X D b c h))
  (@cokernel_adjunction_family_func K C (@additive_preadditive C Prod t Add) t T0 Q (@transf_arrow_diagram_func
  K C B X b)) (@one_cat_native_snake_cokernel_first K C (@additive_preadditive C Prod t Add) C1 t
  (@additive_terminal_object C Prod t Add) T0 P Q A B X D b c h))) Y) u w)
≔ (@one_cat_cospan_kernel_first_reflect_path K C C1 Prod t Add T0 P Q N (@kernel_adjunction_family_func K C
  (@additive_preadditive C Prod t Add) t (@additive_terminal_object C Prod t Add) P (@transf_arrow_diagram_func
  K C (@cokernel_adjunction_family_func K C (@additive_preadditive C Prod t Add) t T0 Q
  (@one_cat_native_snake_alpha_diagram K C (@additive_preadditive C Prod t Add) C1 t (@additive_terminal_object
  C Prod t Add) T0 P A B X D b c h)) (@cokernel_adjunction_family_func K C (@additive_preadditive C Prod t Add)
  t T0 Q (@transf_arrow_diagram_func K C B X b)) (@one_cat_native_snake_cokernel_first K C
  (@additive_preadditive C Prod t Add) C1 t (@additive_terminal_object C Prod t Add) T0 P Q A B X D b c h)))
  (@kernel_adjunction_family_func K C (@additive_preadditive C Prod t Add) t (@additive_terminal_object C Prod t
  Add) P (@transf_arrow_diagram_func K C X D c)) (@cokernel_adjunction_family_func K C (@additive_preadditive C
  Prod t Add) t T0 Q (@one_cat_native_snake_alpha_diagram K C (@additive_preadditive C Prod t Add) C1 t
  (@additive_terminal_object C Prod t Add) T0 P A B X D b c h)) (@kernel_adjunction_family_inclusion_transf K C
  (@additive_preadditive C Prod t Add) t (@additive_terminal_object C Prod t Add) P (@transf_arrow_diagram_func
  K C (@cokernel_adjunction_family_func K C (@additive_preadditive C Prod t Add) t T0 Q
  (@one_cat_native_snake_alpha_diagram K C (@additive_preadditive C Prod t Add) C1 t (@additive_terminal_object
  C Prod t Add) T0 P A B X D b c h)) (@cokernel_adjunction_family_func K C (@additive_preadditive C Prod t Add)
  t T0 Q (@transf_arrow_diagram_func K C B X b)) (@one_cat_native_snake_cokernel_first K C
  (@additive_preadditive C Prod t Add) C1 t (@additive_terminal_object C Prod t Add) T0 P Q A B X D b c h)))
  (@cokernel_adjunction_family_projection_transf K C (@additive_preadditive C Prod t Add) t T0 Q
  (@one_cat_native_snake_alpha_diagram K C (@additive_preadditive C Prod t Add) C1 t (@additive_terminal_object
  C Prod t Add) T0 P A B X D b c h)) (@one_cat_quotient_cokernel_zero K C (@additive_preadditive C Prod t Add)
  C1 t (@additive_terminal_object C Prod t Add) T0 Q (@one_cat_native_snake_alpha_diagram K C
  (@additive_preadditive C Prod t Add) C1 t (@additive_terminal_object C Prod t Add) T0 P A B X D b c h)) Y u w
  p);

// Original q₁ reconstruction and kernel annihilation give π_bκ_cp=0.
symbol one_cat_native_snake_third_cover_image_zero [K C : Cat]
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
  K C B X b))) (@comp_fapp0 (Functor_cat K C) (@one_cat_native_snake_third_cover_source K C C1 Prod t Add T0 P Q
  N A B X D b c h) X (@cokernel_adjunction_family_func K C (@additive_preadditive C Prod t Add) t T0 Q
  (@transf_arrow_diagram_func K C B X b)) (@cokernel_adjunction_family_projection_transf K C
  (@additive_preadditive C Prod t Add) t T0 Q (@transf_arrow_diagram_func K C B X b)) (@comp_fapp0 (Functor_cat
  K C) (@one_cat_native_snake_third_cover_source K C C1 Prod t Add T0 P Q N A B X D b c h)
  (@kernel_adjunction_family_func K C (@additive_preadditive C Prod t Add) t (@additive_terminal_object C Prod t
  Add) P (@transf_arrow_diagram_func K C X D c)) X (@kernel_adjunction_family_inclusion_transf K C
  (@additive_preadditive C Prod t Add) t (@additive_terminal_object C Prod t Add) P (@transf_arrow_diagram_func
  K C X D c)) (@one_cat_native_snake_third_cover_lift K C C1 Prod t Add T0 P Q N A B X D b c h)))
  (@zero_arrow_family_zero_transf K C t (@additive_terminal_object C Prod t Add) T0
  (@one_cat_native_snake_third_cover_source K C C1 Prod t Add T0 P Q N A B X D b c h)
  (@cokernel_adjunction_family_func K C (@additive_preadditive C Prod t Add) t T0 Q (@transf_arrow_diagram_func
  K C B X b))))
≔ (@eq_trans _ _ _ _ (@comp_assoc (Functor_cat K C) (@one_cat_native_snake_third_cover_source K C C1 Prod t Add
  T0 P Q N A B X D b c h) (@kernel_adjunction_family_func K C (@additive_preadditive C Prod t Add) t
  (@additive_terminal_object C Prod t Add) P (@transf_arrow_diagram_func K C X D c)) X
  (@cokernel_adjunction_family_func K C (@additive_preadditive C Prod t Add) t T0 Q (@transf_arrow_diagram_func
  K C B X b)) (@cokernel_adjunction_family_projection_transf K C (@additive_preadditive C Prod t Add) t T0 Q
  (@transf_arrow_diagram_func K C B X b)) (@kernel_adjunction_family_inclusion_transf K C (@additive_preadditive
  C Prod t Add) t (@additive_terminal_object C Prod t Add) P (@transf_arrow_diagram_func K C X D c))
  (@one_cat_native_snake_third_cover_lift K C C1 Prod t Add T0 P Q N A B X D b c h)) (@eq_trans _ _ _ _ (@eq_ap
  (@Transf K C (@kernel_adjunction_family_func K C (@additive_preadditive C Prod t Add) t
  (@additive_terminal_object C Prod t Add) P (@transf_arrow_diagram_func K C X D c))
  (@cokernel_adjunction_family_func K C (@additive_preadditive C Prod t Add) t T0 Q (@transf_arrow_diagram_func
  K C B X b))) (@Transf K C (@one_cat_native_snake_third_cover_source K C C1 Prod t Add T0 P Q N A B X D b c h)
  (@cokernel_adjunction_family_func K C (@additive_preadditive C Prod t Add) t T0 Q (@transf_arrow_diagram_func
  K C B X b))) (λ v : τ (@Transf K C (@kernel_adjunction_family_func K C (@additive_preadditive C Prod t Add) t
  (@additive_terminal_object C Prod t Add) P (@transf_arrow_diagram_func K C X D c))
  (@cokernel_adjunction_family_func K C (@additive_preadditive C Prod t Add) t T0 Q (@transf_arrow_diagram_func
  K C B X b))), (@comp_fapp0 (Functor_cat K C) (@one_cat_native_snake_third_cover_source K C C1 Prod t Add T0 P
  Q N A B X D b c h) (@kernel_adjunction_family_func K C (@additive_preadditive C Prod t Add) t
  (@additive_terminal_object C Prod t Add) P (@transf_arrow_diagram_func K C X D c))
  (@cokernel_adjunction_family_func K C (@additive_preadditive C Prod t Add) t T0 Q (@transf_arrow_diagram_func
  K C B X b)) v (@one_cat_native_snake_third_cover_lift K C C1 Prod t Add T0 P Q N A B X D b c h))) _ _ (@eq_sym
  _ _ _ (@one_cat_native_snake_cokernel_first_reconstruction K C (@additive_preadditive C Prod t Add) C1 t
  (@additive_terminal_object C Prod t Add) T0 P Q A B X D b c h))) (@eq_trans _ _ _ _ (@eq_sym _ _ _
  (@comp_assoc (Functor_cat K C) (@one_cat_native_snake_third_cover_source K C C1 Prod t Add T0 P Q N A B X D b
  c h) (@kernel_adjunction_family_func K C (@additive_preadditive C Prod t Add) t (@additive_terminal_object C
  Prod t Add) P (@transf_arrow_diagram_func K C X D c)) (@cokernel_adjunction_family_func K C
  (@additive_preadditive C Prod t Add) t T0 Q (@one_cat_native_snake_alpha_diagram K C (@additive_preadditive C
  Prod t Add) C1 t (@additive_terminal_object C Prod t Add) T0 P A B X D b c h))
  (@cokernel_adjunction_family_func K C (@additive_preadditive C Prod t Add) t T0 Q (@transf_arrow_diagram_func
  K C B X b)) (@one_cat_native_snake_cokernel_first K C (@additive_preadditive C Prod t Add) C1 t
  (@additive_terminal_object C Prod t Add) T0 P Q A B X D b c h) (@cokernel_adjunction_family_projection_transf
  K C (@additive_preadditive C Prod t Add) t T0 Q (@one_cat_native_snake_alpha_diagram K C
  (@additive_preadditive C Prod t Add) C1 t (@additive_terminal_object C Prod t Add) T0 P A B X D b c h))
  (@one_cat_native_snake_third_cover_lift K C C1 Prod t Add T0 P Q N A B X D b c h))) (@eq_trans _ _ _ _ (@eq_ap
  (@Transf K C (@one_cat_native_snake_third_cover_source K C C1 Prod t Add T0 P Q N A B X D b c h)
  (@cokernel_adjunction_family_func K C (@additive_preadditive C Prod t Add) t T0 Q
  (@one_cat_native_snake_alpha_diagram K C (@additive_preadditive C Prod t Add) C1 t (@additive_terminal_object
  C Prod t Add) T0 P A B X D b c h))) (@Transf K C (@one_cat_native_snake_third_cover_source K C C1 Prod t Add
  T0 P Q N A B X D b c h) (@cokernel_adjunction_family_func K C (@additive_preadditive C Prod t Add) t T0 Q
  (@transf_arrow_diagram_func K C B X b))) (λ v : τ (@Transf K C (@one_cat_native_snake_third_cover_source K C
  C1 Prod t Add T0 P Q N A B X D b c h) (@cokernel_adjunction_family_func K C (@additive_preadditive C Prod t
  Add) t T0 Q (@one_cat_native_snake_alpha_diagram K C (@additive_preadditive C Prod t Add) C1 t
  (@additive_terminal_object C Prod t Add) T0 P A B X D b c h))), (@comp_fapp0 (Functor_cat K C)
  (@one_cat_native_snake_third_cover_source K C C1 Prod t Add T0 P Q N A B X D b c h)
  (@cokernel_adjunction_family_func K C (@additive_preadditive C Prod t Add) t T0 Q
  (@one_cat_native_snake_alpha_diagram K C (@additive_preadditive C Prod t Add) C1 t (@additive_terminal_object
  C Prod t Add) T0 P A B X D b c h)) (@cokernel_adjunction_family_func K C (@additive_preadditive C Prod t Add)
  t T0 Q (@transf_arrow_diagram_func K C B X b)) (@one_cat_native_snake_cokernel_first K C
  (@additive_preadditive C Prod t Add) C1 t (@additive_terminal_object C Prod t Add) T0 P Q A B X D b c h) v)) _
  _ (@eq_sym _ _ _ (@one_cat_native_snake_third_cover_compatibility K C C1 Prod t Add T0 P Q N A B X D b c h)))
  (@eq_trans _ _ _ _ (@comp_assoc (Functor_cat K C) (@one_cat_native_snake_third_cover_source K C C1 Prod t Add
  T0 P Q N A B X D b c h) (@kernel_adjunction_family_func K C (@additive_preadditive C Prod t Add) t
  (@additive_terminal_object C Prod t Add) P (@transf_arrow_diagram_func K C (@cokernel_adjunction_family_func K
  C (@additive_preadditive C Prod t Add) t T0 Q (@one_cat_native_snake_alpha_diagram K C (@additive_preadditive
  C Prod t Add) C1 t (@additive_terminal_object C Prod t Add) T0 P A B X D b c h))
  (@cokernel_adjunction_family_func K C (@additive_preadditive C Prod t Add) t T0 Q (@transf_arrow_diagram_func
  K C B X b)) (@one_cat_native_snake_cokernel_first K C (@additive_preadditive C Prod t Add) C1 t
  (@additive_terminal_object C Prod t Add) T0 P Q A B X D b c h))) (@cokernel_adjunction_family_func K C
  (@additive_preadditive C Prod t Add) t T0 Q (@one_cat_native_snake_alpha_diagram K C (@additive_preadditive C
  Prod t Add) C1 t (@additive_terminal_object C Prod t Add) T0 P A B X D b c h))
  (@cokernel_adjunction_family_func K C (@additive_preadditive C Prod t Add) t T0 Q (@transf_arrow_diagram_func
  K C B X b)) (@one_cat_native_snake_cokernel_first K C (@additive_preadditive C Prod t Add) C1 t
  (@additive_terminal_object C Prod t Add) T0 P Q A B X D b c h) (@kernel_adjunction_family_inclusion_transf K C
  (@additive_preadditive C Prod t Add) t (@additive_terminal_object C Prod t Add) P (@transf_arrow_diagram_func
  K C (@cokernel_adjunction_family_func K C (@additive_preadditive C Prod t Add) t T0 Q
  (@one_cat_native_snake_alpha_diagram K C (@additive_preadditive C Prod t Add) C1 t (@additive_terminal_object
  C Prod t Add) T0 P A B X D b c h)) (@cokernel_adjunction_family_func K C (@additive_preadditive C Prod t Add)
  t T0 Q (@transf_arrow_diagram_func K C B X b)) (@one_cat_native_snake_cokernel_first K C
  (@additive_preadditive C Prod t Add) C1 t (@additive_terminal_object C Prod t Add) T0 P Q A B X D b c h)))
  (@one_cat_native_snake_third_cover_projection K C C1 Prod t Add T0 P Q N A B X D b c h)) (@eq_trans _ _ _ _
  (@eq_ap (@Transf K C (@kernel_adjunction_family_func K C (@additive_preadditive C Prod t Add) t
  (@additive_terminal_object C Prod t Add) P (@transf_arrow_diagram_func K C (@cokernel_adjunction_family_func K
  C (@additive_preadditive C Prod t Add) t T0 Q (@one_cat_native_snake_alpha_diagram K C (@additive_preadditive
  C Prod t Add) C1 t (@additive_terminal_object C Prod t Add) T0 P A B X D b c h))
  (@cokernel_adjunction_family_func K C (@additive_preadditive C Prod t Add) t T0 Q (@transf_arrow_diagram_func
  K C B X b)) (@one_cat_native_snake_cokernel_first K C (@additive_preadditive C Prod t Add) C1 t
  (@additive_terminal_object C Prod t Add) T0 P Q A B X D b c h))) (@cokernel_adjunction_family_func K C
  (@additive_preadditive C Prod t Add) t T0 Q (@transf_arrow_diagram_func K C B X b))) (@Transf K C
  (@one_cat_native_snake_third_cover_source K C C1 Prod t Add T0 P Q N A B X D b c h)
  (@cokernel_adjunction_family_func K C (@additive_preadditive C Prod t Add) t T0 Q (@transf_arrow_diagram_func
  K C B X b))) (λ v : τ (@Transf K C (@kernel_adjunction_family_func K C (@additive_preadditive C Prod t Add) t
  (@additive_terminal_object C Prod t Add) P (@transf_arrow_diagram_func K C (@cokernel_adjunction_family_func K
  C (@additive_preadditive C Prod t Add) t T0 Q (@one_cat_native_snake_alpha_diagram K C (@additive_preadditive
  C Prod t Add) C1 t (@additive_terminal_object C Prod t Add) T0 P A B X D b c h))
  (@cokernel_adjunction_family_func K C (@additive_preadditive C Prod t Add) t T0 Q (@transf_arrow_diagram_func
  K C B X b)) (@one_cat_native_snake_cokernel_first K C (@additive_preadditive C Prod t Add) C1 t
  (@additive_terminal_object C Prod t Add) T0 P Q A B X D b c h))) (@cokernel_adjunction_family_func K C
  (@additive_preadditive C Prod t Add) t T0 Q (@transf_arrow_diagram_func K C B X b))), (@comp_fapp0
  (Functor_cat K C) (@one_cat_native_snake_third_cover_source K C C1 Prod t Add T0 P Q N A B X D b c h)
  (@kernel_adjunction_family_func K C (@additive_preadditive C Prod t Add) t (@additive_terminal_object C Prod t
  Add) P (@transf_arrow_diagram_func K C (@cokernel_adjunction_family_func K C (@additive_preadditive C Prod t
  Add) t T0 Q (@one_cat_native_snake_alpha_diagram K C (@additive_preadditive C Prod t Add) C1 t
  (@additive_terminal_object C Prod t Add) T0 P A B X D b c h)) (@cokernel_adjunction_family_func K C
  (@additive_preadditive C Prod t Add) t T0 Q (@transf_arrow_diagram_func K C B X b))
  (@one_cat_native_snake_cokernel_first K C (@additive_preadditive C Prod t Add) C1 t (@additive_terminal_object
  C Prod t Add) T0 P Q A B X D b c h))) (@cokernel_adjunction_family_func K C (@additive_preadditive C Prod t
  Add) t T0 Q (@transf_arrow_diagram_func K C B X b)) v (@one_cat_native_snake_third_cover_projection K C C1
  Prod t Add T0 P Q N A B X D b c h))) _ _ (@one_cat_kernel_family_annihilation_path K C (@additive_preadditive
  C Prod t Add) C1 t (@additive_terminal_object C Prod t Add) T0 P (@transf_arrow_diagram_func K C
  (@cokernel_adjunction_family_func K C (@additive_preadditive C Prod t Add) t T0 Q
  (@one_cat_native_snake_alpha_diagram K C (@additive_preadditive C Prod t Add) C1 t (@additive_terminal_object
  C Prod t Add) T0 P A B X D b c h)) (@cokernel_adjunction_family_func K C (@additive_preadditive C Prod t Add)
  t T0 Q (@transf_arrow_diagram_func K C B X b)) (@one_cat_native_snake_cokernel_first K C
  (@additive_preadditive C Prod t Add) C1 t (@additive_terminal_object C Prod t Add) T0 P Q A B X D b c h))))
  (@one_cat_zero_family_precompose_path K C C1 t (@additive_terminal_object C Prod t Add) T0
  (@one_cat_native_snake_third_cover_source K C C1 Prod t Add T0 P Q N A B X D b c h)
  (@kernel_adjunction_family_func K C (@additive_preadditive C Prod t Add) t (@additive_terminal_object C Prod t
  Add) P (@transf_arrow_diagram_func K C (@cokernel_adjunction_family_func K C (@additive_preadditive C Prod t
  Add) t T0 Q (@one_cat_native_snake_alpha_diagram K C (@additive_preadditive C Prod t Add) C1 t
  (@additive_terminal_object C Prod t Add) T0 P A B X D b c h)) (@cokernel_adjunction_family_func K C
  (@additive_preadditive C Prod t Add) t T0 Q (@transf_arrow_diagram_func K C B X b))
  (@one_cat_native_snake_cokernel_first K C (@additive_preadditive C Prod t Add) C1 t (@additive_terminal_object
  C Prod t Add) T0 P Q A B X D b c h))) (@cokernel_adjunction_family_func K C (@additive_preadditive C Prod t
  Add) t T0 Q (@transf_arrow_diagram_func K C B X b)) (@one_cat_native_snake_third_cover_projection K C C1 Prod
  t Add T0 P Q N A B X D b c h))))))));

// Lift κ_cp into the original image kernel on the original Q-arrow of b.
symbol one_cat_native_snake_third_cover_image_lift [K C : Cat]
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
  : τ (@Transf K C (@one_cat_native_snake_third_cover_source K C C1 Prod t Add T0 P Q N A B X D b c h)
  (@comp_cat_fapp0 K (Functor_cat WalkingArrow_cat C) C (@adjunction_image_func C (@additive_preadditive C Prod
  t Add) t (@additive_terminal_object C Prod t Add) T0 P Q) (@transf_arrow_diagram_func K C B X b)))
≔ (@one_cat_kernel_family_lift K C (@additive_preadditive C Prod t Add) C1 t (@additive_terminal_object C Prod t
  Add) T0 P (@one_cat_native_snake_third_cover_source K C C1 Prod t Add T0 P Q N A B X D b c h) (@comp_cat_fapp0
  K (Functor_cat WalkingArrow_cat C) (Functor_cat WalkingArrow_cat C) (@cokernel_adjunction_arrow_func C
  (@additive_preadditive C Prod t Add) t T0 Q) (@transf_arrow_diagram_func K C B X b)) (@comp_fapp0 (Functor_cat
  K C) (@one_cat_native_snake_third_cover_source K C C1 Prod t Add T0 P Q N A B X D b c h)
  (@kernel_adjunction_family_func K C (@additive_preadditive C Prod t Add) t (@additive_terminal_object C Prod t
  Add) P (@transf_arrow_diagram_func K C X D c)) X (@kernel_adjunction_family_inclusion_transf K C
  (@additive_preadditive C Prod t Add) t (@additive_terminal_object C Prod t Add) P (@transf_arrow_diagram_func
  K C X D c)) (@one_cat_native_snake_third_cover_lift K C C1 Prod t Add T0 P Q N A B X D b c h))
  (@one_cat_native_snake_third_cover_image_zero K C C1 Prod t Add T0 P Q N A B X D b c h));

// The original image inclusion reconstructs κ_cp.
symbol one_cat_native_snake_third_cover_image_reconstruction [K C : Cat]
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
  : τ (@= (@Transf K C (@one_cat_native_snake_third_cover_source K C C1 Prod t Add T0 P Q N A B X D b c h) X)
  (@comp_fapp0 (Functor_cat K C) (@one_cat_native_snake_third_cover_source K C C1 Prod t Add T0 P Q N A B X D b
  c h) (@comp_cat_fapp0 K (Functor_cat WalkingArrow_cat C) C (@adjunction_image_func C (@additive_preadditive C
  Prod t Add) t (@additive_terminal_object C Prod t Add) T0 P Q) (@transf_arrow_diagram_func K C B X b)) X
  (@kernel_adjunction_family_inclusion_transf K C (@additive_preadditive C Prod t Add) t
  (@additive_terminal_object C Prod t Add) P (@comp_cat_fapp0 K (Functor_cat WalkingArrow_cat C) (Functor_cat
  WalkingArrow_cat C) (@cokernel_adjunction_arrow_func C (@additive_preadditive C Prod t Add) t T0 Q)
  (@transf_arrow_diagram_func K C B X b))) (@one_cat_native_snake_third_cover_image_lift K C C1 Prod t Add T0 P
  Q N A B X D b c h)) (@comp_fapp0 (Functor_cat K C) (@one_cat_native_snake_third_cover_source K C C1 Prod t Add
  T0 P Q N A B X D b c h) (@kernel_adjunction_family_func K C (@additive_preadditive C Prod t Add) t
  (@additive_terminal_object C Prod t Add) P (@transf_arrow_diagram_func K C X D c)) X
  (@kernel_adjunction_family_inclusion_transf K C (@additive_preadditive C Prod t Add) t
  (@additive_terminal_object C Prod t Add) P (@transf_arrow_diagram_func K C X D c))
  (@one_cat_native_snake_third_cover_lift K C C1 Prod t Add T0 P Q N A B X D b c h)))
≔ (@one_cat_kernel_family_lift_ambient_reconstruction K C (@additive_preadditive C Prod t Add) C1 t
  (@additive_terminal_object C Prod t Add) T0 P (@one_cat_native_snake_third_cover_source K C C1 Prod t Add T0 P
  Q N A B X D b c h) (@comp_cat_fapp0 K (Functor_cat WalkingArrow_cat C) (Functor_cat WalkingArrow_cat C)
  (@cokernel_adjunction_arrow_func C (@additive_preadditive C Prod t Add) t T0 Q) (@transf_arrow_diagram_func K
  C B X b)) (@comp_fapp0 (Functor_cat K C) (@one_cat_native_snake_third_cover_source K C C1 Prod t Add T0 P Q N
  A B X D b c h) (@kernel_adjunction_family_func K C (@additive_preadditive C Prod t Add) t
  (@additive_terminal_object C Prod t Add) P (@transf_arrow_diagram_func K C X D c)) X
  (@kernel_adjunction_family_inclusion_transf K C (@additive_preadditive C Prod t Add) t
  (@additive_terminal_object C Prod t Add) P (@transf_arrow_diagram_func K C X D c))
  (@one_cat_native_snake_third_cover_lift K C C1 Prod t Add T0 P Q N A B X D b c h))
  (@one_cat_native_snake_third_cover_image_zero K C C1 Prod t Add T0 P Q N A B X D b c h));

// The original source-image cover of b has zero cokernel projection.
symbol one_cat_native_snake_third_middle_image_cokernel_zero [K C : Cat]
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
  : τ (@= (@Transf K C (@comp_cat_fapp0 K (Functor_cat WalkingArrow_cat C) C (@adjunction_image_func C
  (@additive_preadditive C Prod t Add) t (@additive_terminal_object C Prod t Add) T0 P Q)
  (@transf_arrow_diagram_func K C B X b)) (@cokernel_adjunction_family_func K C (@additive_preadditive C Prod t
  Add) t T0 Q (@transf_arrow_diagram_func K C B (@comp_cat_fapp0 K (Functor_cat WalkingArrow_cat C) C
  (@adjunction_image_func C (@additive_preadditive C Prod t Add) t (@additive_terminal_object C Prod t Add) T0 P
  Q) (@transf_arrow_diagram_func K C B X b)) (@one_cat_image_family_source_transf K C (@additive_preadditive C
  Prod t Add) C1 t (@additive_terminal_object C Prod t Add) T0 P Q (@transf_arrow_diagram_func K C B X b)))))
  (@cokernel_adjunction_family_projection_transf K C (@additive_preadditive C Prod t Add) t T0 Q
  (@transf_arrow_diagram_func K C B (@comp_cat_fapp0 K (Functor_cat WalkingArrow_cat C) C
  (@adjunction_image_func C (@additive_preadditive C Prod t Add) t (@additive_terminal_object C Prod t Add) T0 P
  Q) (@transf_arrow_diagram_func K C B X b)) (@one_cat_image_family_source_transf K C (@additive_preadditive C
  Prod t Add) C1 t (@additive_terminal_object C Prod t Add) T0 P Q (@transf_arrow_diagram_func K C B X b))))
  (@zero_arrow_family_zero_transf K C t (@additive_terminal_object C Prod t Add) T0 (@comp_cat_fapp0 K
  (Functor_cat WalkingArrow_cat C) C (@adjunction_image_func C (@additive_preadditive C Prod t Add) t
  (@additive_terminal_object C Prod t Add) T0 P Q) (@transf_arrow_diagram_func K C B X b))
  (@cokernel_adjunction_family_func K C (@additive_preadditive C Prod t Add) t T0 Q (@transf_arrow_diagram_func
  K C B (@comp_cat_fapp0 K (Functor_cat WalkingArrow_cat C) C (@adjunction_image_func C (@additive_preadditive C
  Prod t Add) t (@additive_terminal_object C Prod t Add) T0 P Q) (@transf_arrow_diagram_func K C B X b))
  (@one_cat_image_family_source_transf K C (@additive_preadditive C Prod t Add) C1 t (@additive_terminal_object
  C Prod t Add) T0 P Q (@transf_arrow_diagram_func K C B X b))))))
≔ (@one_cat_image_family_source_reflect_path K C (@additive_preadditive C Prod t Add) C1 t
  (@additive_terminal_object C Prod t Add) T0 P Q N (@transf_arrow_diagram_func K C B X b)
  (@cokernel_adjunction_family_func K C (@additive_preadditive C Prod t Add) t T0 Q (@transf_arrow_diagram_func
  K C B (@comp_cat_fapp0 K (Functor_cat WalkingArrow_cat C) C (@adjunction_image_func C (@additive_preadditive C
  Prod t Add) t (@additive_terminal_object C Prod t Add) T0 P Q) (@transf_arrow_diagram_func K C B X b))
  (@one_cat_image_family_source_transf K C (@additive_preadditive C Prod t Add) C1 t (@additive_terminal_object
  C Prod t Add) T0 P Q (@transf_arrow_diagram_func K C B X b)))) (@cokernel_adjunction_family_projection_transf
  K C (@additive_preadditive C Prod t Add) t T0 Q (@transf_arrow_diagram_func K C B (@comp_cat_fapp0 K
  (Functor_cat WalkingArrow_cat C) C (@adjunction_image_func C (@additive_preadditive C Prod t Add) t
  (@additive_terminal_object C Prod t Add) T0 P Q) (@transf_arrow_diagram_func K C B X b))
  (@one_cat_image_family_source_transf K C (@additive_preadditive C Prod t Add) C1 t (@additive_terminal_object
  C Prod t Add) T0 P Q (@transf_arrow_diagram_func K C B X b)))) (@zero_arrow_family_zero_transf K C t
  (@additive_terminal_object C Prod t Add) T0 (@comp_cat_fapp0 K (Functor_cat WalkingArrow_cat C) C
  (@adjunction_image_func C (@additive_preadditive C Prod t Add) t (@additive_terminal_object C Prod t Add) T0 P
  Q) (@transf_arrow_diagram_func K C B X b)) (@cokernel_adjunction_family_func K C (@additive_preadditive C Prod
  t Add) t T0 Q (@transf_arrow_diagram_func K C B (@comp_cat_fapp0 K (Functor_cat WalkingArrow_cat C) C
  (@adjunction_image_func C (@additive_preadditive C Prod t Add) t (@additive_terminal_object C Prod t Add) T0 P
  Q) (@transf_arrow_diagram_func K C B X b)) (@one_cat_image_family_source_transf K C (@additive_preadditive C
  Prod t Add) C1 t (@additive_terminal_object C Prod t Add) T0 P Q (@transf_arrow_diagram_func K C B X b)))))
  (@eq_trans _ _ _ _ (@one_cat_cokernel_family_annihilation_path K C (@additive_preadditive C Prod t Add) C1 t
  (@additive_terminal_object C Prod t Add) T0 Q (@transf_arrow_diagram_func K C B (@comp_cat_fapp0 K
  (Functor_cat WalkingArrow_cat C) C (@adjunction_image_func C (@additive_preadditive C Prod t Add) t
  (@additive_terminal_object C Prod t Add) T0 P Q) (@transf_arrow_diagram_func K C B X b))
  (@one_cat_image_family_source_transf K C (@additive_preadditive C Prod t Add) C1 t (@additive_terminal_object
  C Prod t Add) T0 P Q (@transf_arrow_diagram_func K C B X b)))) (@eq_sym _ _ _
  (@one_cat_zero_family_precompose_path K C C1 t (@additive_terminal_object C Prod t Add) T0 B (@comp_cat_fapp0
  K (Functor_cat WalkingArrow_cat C) C (@adjunction_image_func C (@additive_preadditive C Prod t Add) t
  (@additive_terminal_object C Prod t Add) T0 P Q) (@transf_arrow_diagram_func K C B X b))
  (@cokernel_adjunction_family_func K C (@additive_preadditive C Prod t Add) t T0 Q (@transf_arrow_diagram_func
  K C B (@comp_cat_fapp0 K (Functor_cat WalkingArrow_cat C) C (@adjunction_image_func C (@additive_preadditive C
  Prod t Add) t (@additive_terminal_object C Prod t Add) T0 P Q) (@transf_arrow_diagram_func K C B X b))
  (@one_cat_image_family_source_transf K C (@additive_preadditive C Prod t Add) C1 t (@additive_terminal_object
  C Prod t Add) T0 P Q (@transf_arrow_diagram_func K C B X b)))) (@one_cat_image_family_source_transf K C
  (@additive_preadditive C Prod t Add) C1 t (@additive_terminal_object C Prod t Add) T0 P Q
  (@transf_arrow_diagram_func K C B X b))))));

// The second whole cospan kernel compares the image lift with s_b:B⇒Im(b).
symbol one_cat_native_snake_third_middle_cover_source [K C : Cat]
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
  : τ (Functor K C)
≔ (@one_cat_cospan_kernel_func K C C1 Prod t Add T0 P Q (@one_cat_native_snake_third_cover_source K C C1 Prod t
  Add T0 P Q N A B X D b c h) B (@comp_cat_fapp0 K (Functor_cat WalkingArrow_cat C) C (@adjunction_image_func C
  (@additive_preadditive C Prod t Add) t (@additive_terminal_object C Prod t Add) T0 P Q)
  (@transf_arrow_diagram_func K C B X b)) (@one_cat_native_snake_third_cover_image_lift K C C1 Prod t Add T0 P Q
  N A B X D b c h) (@one_cat_image_family_source_transf K C (@additive_preadditive C Prod t Add) C1 t
  (@additive_terminal_object C Prod t Add) T0 P Q (@transf_arrow_diagram_func K C B X b)));

// Its original first projection s:V⇒L is the second cover.
symbol one_cat_native_snake_third_middle_cover_first [K C : Cat]
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
  : τ (@Transf K C (@one_cat_native_snake_third_middle_cover_source K C C1 Prod t Add T0 P Q N A B X D b c h)
  (@one_cat_native_snake_third_cover_source K C C1 Prod t Add T0 P Q N A B X D b c h))
≔ (@one_cat_cospan_kernel_first K C C1 Prod t Add T0 P Q (@one_cat_native_snake_third_cover_source K C C1 Prod t
  Add T0 P Q N A B X D b c h) B (@comp_cat_fapp0 K (Functor_cat WalkingArrow_cat C) C (@adjunction_image_func C
  (@additive_preadditive C Prod t Add) t (@additive_terminal_object C Prod t Add) T0 P Q)
  (@transf_arrow_diagram_func K C B X b)) (@one_cat_native_snake_third_cover_image_lift K C C1 Prod t Add T0 P Q
  N A B X D b c h) (@one_cat_image_family_source_transf K C (@additive_preadditive C Prod t Add) C1 t
  (@additive_terminal_object C Prod t Add) T0 P Q (@transf_arrow_diagram_func K C B X b)));

// Its original second projection x:V⇒B gives the b representative.
symbol one_cat_native_snake_third_middle_cover_second [K C : Cat]
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
  : τ (@Transf K C (@one_cat_native_snake_third_middle_cover_source K C C1 Prod t Add T0 P Q N A B X D b c h) B)
≔ (@one_cat_cospan_kernel_second K C C1 Prod t Add T0 P Q (@one_cat_native_snake_third_cover_source K C C1 Prod
  t Add T0 P Q N A B X D b c h) B (@comp_cat_fapp0 K (Functor_cat WalkingArrow_cat C) C (@adjunction_image_func
  C (@additive_preadditive C Prod t Add) t (@additive_terminal_object C Prod t Add) T0 P Q)
  (@transf_arrow_diagram_func K C B X b)) (@one_cat_native_snake_third_cover_image_lift K C C1 Prod t Add T0 P Q
  N A B X D b c h) (@one_cat_image_family_source_transf K C (@additive_preadditive C Prod t Add) C1 t
  (@additive_terminal_object C Prod t Add) T0 P Q (@transf_arrow_diagram_func K C B X b)));

// The original projections satisfy λs=s_bx wholly.
symbol one_cat_native_snake_third_middle_cover_compatibility [K C : Cat]
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
  h) (@comp_cat_fapp0 K (Functor_cat WalkingArrow_cat C) C (@adjunction_image_func C (@additive_preadditive C
  Prod t Add) t (@additive_terminal_object C Prod t Add) T0 P Q) (@transf_arrow_diagram_func K C B X b)))
  (@comp_fapp0 (Functor_cat K C) (@one_cat_native_snake_third_middle_cover_source K C C1 Prod t Add T0 P Q N A B
  X D b c h) (@one_cat_native_snake_third_cover_source K C C1 Prod t Add T0 P Q N A B X D b c h)
  (@comp_cat_fapp0 K (Functor_cat WalkingArrow_cat C) C (@adjunction_image_func C (@additive_preadditive C Prod
  t Add) t (@additive_terminal_object C Prod t Add) T0 P Q) (@transf_arrow_diagram_func K C B X b))
  (@one_cat_native_snake_third_cover_image_lift K C C1 Prod t Add T0 P Q N A B X D b c h)
  (@one_cat_native_snake_third_middle_cover_first K C C1 Prod t Add T0 P Q N A B X D b c h)) (@comp_fapp0
  (Functor_cat K C) (@one_cat_native_snake_third_middle_cover_source K C C1 Prod t Add T0 P Q N A B X D b c h) B
  (@comp_cat_fapp0 K (Functor_cat WalkingArrow_cat C) C (@adjunction_image_func C (@additive_preadditive C Prod
  t Add) t (@additive_terminal_object C Prod t Add) T0 P Q) (@transf_arrow_diagram_func K C B X b))
  (@one_cat_image_family_source_transf K C (@additive_preadditive C Prod t Add) C1 t (@additive_terminal_object
  C Prod t Add) T0 P Q (@transf_arrow_diagram_func K C B X b)) (@one_cat_native_snake_third_middle_cover_second
  K C C1 Prod t Add T0 P Q N A B X D b c h)))
≔ (@one_cat_cospan_kernel_compatibility K C C1 Prod t Add T0 P Q (@one_cat_native_snake_third_cover_source K C
  C1 Prod t Add T0 P Q N A B X D b c h) B (@comp_cat_fapp0 K (Functor_cat WalkingArrow_cat C) C
  (@adjunction_image_func C (@additive_preadditive C Prod t Add) t (@additive_terminal_object C Prod t Add) T0 P
  Q) (@transf_arrow_diagram_func K C B X b)) (@one_cat_native_snake_third_cover_image_lift K C C1 Prod t Add T0
  P Q N A B X D b c h) (@one_cat_image_family_source_transf K C (@additive_preadditive C Prod t Add) C1 t
  (@additive_terminal_object C Prod t Add) T0 P Q (@transf_arrow_diagram_func K C B X b)));

// The derived second cover s cancels whole maps out of L.
symbol one_cat_native_snake_third_middle_cover_reflect_path [K C : Cat]
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
  (Y : τ (Functor K C)) (u w : τ (@Transf K C (@one_cat_native_snake_third_cover_source K C C1 Prod t Add T0 P Q
  N A B X D b c h) Y))
  (p : τ (@= (@Transf K C (@one_cat_native_snake_third_middle_cover_source K C C1 Prod t Add T0 P Q N A B X D b
  c h) Y) (@comp_fapp0 (Functor_cat K C) (@one_cat_native_snake_third_middle_cover_source K C C1 Prod t Add T0 P
  Q N A B X D b c h) (@one_cat_native_snake_third_cover_source K C C1 Prod t Add T0 P Q N A B X D b c h) Y u
  (@one_cat_native_snake_third_middle_cover_first K C C1 Prod t Add T0 P Q N A B X D b c h)) (@comp_fapp0
  (Functor_cat K C) (@one_cat_native_snake_third_middle_cover_source K C C1 Prod t Add T0 P Q N A B X D b c h)
  (@one_cat_native_snake_third_cover_source K C C1 Prod t Add T0 P Q N A B X D b c h) Y w
  (@one_cat_native_snake_third_middle_cover_first K C C1 Prod t Add T0 P Q N A B X D b c h))))
  : τ (@= (@Transf K C (@one_cat_native_snake_third_cover_source K C C1 Prod t Add T0 P Q N A B X D b c h) Y) u
  w)
≔ (@one_cat_cospan_kernel_first_reflect_path K C C1 Prod t Add T0 P Q N
  (@one_cat_native_snake_third_cover_source K C C1 Prod t Add T0 P Q N A B X D b c h) B (@comp_cat_fapp0 K
  (Functor_cat WalkingArrow_cat C) C (@adjunction_image_func C (@additive_preadditive C Prod t Add) t
  (@additive_terminal_object C Prod t Add) T0 P Q) (@transf_arrow_diagram_func K C B X b))
  (@one_cat_native_snake_third_cover_image_lift K C C1 Prod t Add T0 P Q N A B X D b c h)
  (@one_cat_image_family_source_transf K C (@additive_preadditive C Prod t Add) C1 t (@additive_terminal_object
  C Prod t Add) T0 P Q (@transf_arrow_diagram_func K C B X b))
  (@one_cat_native_snake_third_middle_image_cokernel_zero K C C1 Prod t Add T0 P Q N A B X D b c h) Y u w p);
