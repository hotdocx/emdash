/* The original source-image cover induces the first exactness representatives. */
require open emdash.emdash3_2_one_cat_native_snake_first_kernel_comparison;

// The original image-source cover cancels to show its own cokernel projection zero.
symbol one_cat_native_snake_image_source_cokernel_zero [K C : Cat] [S : τ (@PreadditiveCategory C)]
  (C1 : τ (IsNCat (cat_succ cat_zero) C)) [t : τ (Obj C)]
  (T : τ (@TerminalObject C t)) (T0 : τ (@TerminalObject (Op_cat C) t))
  (P : τ (@KernelAdjunctionStructure C S t T)) (Q : τ (@CokernelAdjunctionStructure C S t T0))
  (N : τ (@OneCatAdjunctionNormality C S C1 t T T0 P Q))
  [A B X D : τ (Functor K C)] (b : τ (@Transf K C B X)) (c : τ (@Transf K C X D))
  (h : τ (@NativeSnakeInput K C t T A B X D b c))
  : τ (@= (@Transf K C (@one_cat_native_snake_image_func K C S C1 t T T0 P Q A B X D b c h)
    (@cokernel_adjunction_family_func K C S t T0 Q (@transf_arrow_diagram_func K C A
    (@one_cat_native_snake_image_func K C S C1 t T T0 P Q A B X D b c h) (@one_cat_native_snake_source_image K C
    S C1 t T T0 P Q A B X D b c h)))) (@cokernel_adjunction_family_projection_transf K C S t T0 Q
    (@transf_arrow_diagram_func K C A (@one_cat_native_snake_image_func K C S C1 t T T0 P Q A B X D b c h)
    (@one_cat_native_snake_source_image K C S C1 t T T0 P Q A B X D b c h))) (@zero_arrow_family_zero_transf K C
    t T T0 (@one_cat_native_snake_image_func K C S C1 t T T0 P Q A B X D b c h)
    (@cokernel_adjunction_family_func K C S t T0 Q (@transf_arrow_diagram_func K C A
    (@one_cat_native_snake_image_func K C S C1 t T T0 P Q A B X D b c h) (@one_cat_native_snake_source_image K C
    S C1 t T T0 P Q A B X D b c h)))))
≔ (@one_cat_image_family_source_reflect_path K C S C1 t T T0 P Q N (@native_snake_incoming_diagram K C t T A B X
  D b c h) (@cokernel_adjunction_family_func K C S t T0 Q (@transf_arrow_diagram_func K C A
  (@one_cat_native_snake_image_func K C S C1 t T T0 P Q A B X D b c h) (@one_cat_native_snake_source_image K C S
  C1 t T T0 P Q A B X D b c h))) (@cokernel_adjunction_family_projection_transf K C S t T0 Q
  (@transf_arrow_diagram_func K C A (@one_cat_native_snake_image_func K C S C1 t T T0 P Q A B X D b c h)
  (@one_cat_native_snake_source_image K C S C1 t T T0 P Q A B X D b c h))) (@zero_arrow_family_zero_transf K C t
  T T0 (@one_cat_native_snake_image_func K C S C1 t T T0 P Q A B X D b c h) (@cokernel_adjunction_family_func K
  C S t T0 Q (@transf_arrow_diagram_func K C A (@one_cat_native_snake_image_func K C S C1 t T T0 P Q A B X D b c
  h) (@one_cat_native_snake_source_image K C S C1 t T T0 P Q A B X D b c h)))) (@eq_trans _ _ _ _
  (@one_cat_cokernel_family_annihilation_path K C S C1 t T T0 Q (@transf_arrow_diagram_func K C A
  (@one_cat_native_snake_image_func K C S C1 t T T0 P Q A B X D b c h) (@one_cat_native_snake_source_image K C S
  C1 t T T0 P Q A B X D b c h))) (@eq_sym _ _ _ (@one_cat_zero_family_precompose_path K C C1 t T T0 A
  (@one_cat_native_snake_image_func K C S C1 t T T0 P Q A B X D b c h) (@cokernel_adjunction_family_func K C S t
  T0 Q (@transf_arrow_diagram_func K C A (@one_cat_native_snake_image_func K C S C1 t T T0 P Q A B X D b c h)
  (@one_cat_native_snake_source_image K C S C1 t T T0 P Q A B X D b c h))) (@one_cat_native_snake_source_image K
  C S C1 t T T0 P Q A B X D b c h)))));

// The original pullback-cover source L=K(v∘s_a).
symbol one_cat_native_snake_first_cover_source [K C : Cat] [S : τ (@PreadditiveCategory C)]
  (C1 : τ (IsNCat (cat_succ cat_zero) C)) [t : τ (Obj C)]
  (T : τ (@TerminalObject C t)) (T0 : τ (@TerminalObject (Op_cat C) t))
  (P : τ (@KernelAdjunctionStructure C S t T)) (Q : τ (@CokernelAdjunctionStructure C S t T0))
  [A B X D : τ (Functor K C)] (b : τ (@Transf K C B X)) (c : τ (@Transf K C X D))
  (h : τ (@NativeSnakeInput K C t T A B X D b c))
  : τ (Functor K C)
≔ (@kernel_precomposition_family_func K C S t T P A (@transf_arrow_diagram_func K C
  (@one_cat_native_snake_image_func K C S C1 t T T0 P Q A B X D b c h) (@kernel_adjunction_family_func K C S t T
  P (@transf_arrow_diagram_func K C X D c)) (@one_cat_native_snake_image_lift K C S C1 t T T0 P Q A B X D b c
  h)) (@one_cat_native_snake_source_image K C S C1 t T T0 P Q A B X D b c h));

// The original first projection L⇒A.
symbol one_cat_native_snake_first_cover_first [K C : Cat] [S : τ (@PreadditiveCategory C)]
  (C1 : τ (IsNCat (cat_succ cat_zero) C)) [t : τ (Obj C)]
  (T : τ (@TerminalObject C t)) (T0 : τ (@TerminalObject (Op_cat C) t))
  (P : τ (@KernelAdjunctionStructure C S t T)) (Q : τ (@CokernelAdjunctionStructure C S t T0))
  [A B X D : τ (Functor K C)] (b : τ (@Transf K C B X)) (c : τ (@Transf K C X D))
  (h : τ (@NativeSnakeInput K C t T A B X D b c))
  : τ (@Transf K C (@one_cat_native_snake_first_cover_source K C S C1 t T T0 P Q A B X D b c h) A)
≔ (@kernel_precomposition_first_transf K C S t T P A (@transf_arrow_diagram_func K C
  (@one_cat_native_snake_image_func K C S C1 t T T0 P Q A B X D b c h) (@kernel_adjunction_family_func K C S t T
  P (@transf_arrow_diagram_func K C X D c)) (@one_cat_native_snake_image_lift K C S C1 t T T0 P Q A B X D b c
  h)) (@one_cat_native_snake_source_image K C S C1 t T T0 P Q A B X D b c h));

// The original induced map L⇒K(v).
symbol one_cat_native_snake_first_cover_transf [K C : Cat] [S : τ (@PreadditiveCategory C)]
  (C1 : τ (IsNCat (cat_succ cat_zero) C)) [t : τ (Obj C)]
  (T : τ (@TerminalObject C t)) (T0 : τ (@TerminalObject (Op_cat C) t))
  (P : τ (@KernelAdjunctionStructure C S t T)) (Q : τ (@CokernelAdjunctionStructure C S t T0))
  [A B X D : τ (Functor K C)] (b : τ (@Transf K C B X)) (c : τ (@Transf K C X D))
  (h : τ (@NativeSnakeInput K C t T A B X D b c))
  : τ (@Transf K C (@one_cat_native_snake_first_cover_source K C S C1 t T T0 P Q A B X D b c h)
    (@kernel_adjunction_family_func K C S t T P (@transf_arrow_diagram_func K C
    (@one_cat_native_snake_image_func K C S C1 t T T0 P Q A B X D b c h) (@kernel_adjunction_family_func K C S t
    T P (@transf_arrow_diagram_func K C X D c)) (@one_cat_native_snake_image_lift K C S C1 t T T0 P Q A B X D b
    c h))))
≔ (@one_cat_kernel_precomposition_second_transf K C S C1 t T T0 P A (@transf_arrow_diagram_func K C
  (@one_cat_native_snake_image_func K C S C1 t T T0 P Q A B X D b c h) (@kernel_adjunction_family_func K C S t T
  P (@transf_arrow_diagram_func K C X D c)) (@one_cat_native_snake_image_lift K C S C1 t T T0 P Q A B X D b c
  h)) (@one_cat_native_snake_source_image K C S C1 t T T0 P Q A B X D b c h));

// Native kernel-precomposition reconstruction gives κ_v r_L=s_a j_L.
symbol one_cat_native_snake_first_cover_square_path [K C : Cat] [S : τ (@PreadditiveCategory C)]
  (C1 : τ (IsNCat (cat_succ cat_zero) C)) [t : τ (Obj C)]
  (T : τ (@TerminalObject C t)) (T0 : τ (@TerminalObject (Op_cat C) t))
  (P : τ (@KernelAdjunctionStructure C S t T)) (Q : τ (@CokernelAdjunctionStructure C S t T0))
  [A B X D : τ (Functor K C)] (b : τ (@Transf K C B X)) (c : τ (@Transf K C X D))
  (h : τ (@NativeSnakeInput K C t T A B X D b c))
  : τ (@= (@Transf K C (@one_cat_native_snake_first_cover_source K C S C1 t T T0 P Q A B X D b c h)
    (@one_cat_native_snake_image_func K C S C1 t T T0 P Q A B X D b c h)) (@comp_fapp0 (Functor_cat K C)
    (@one_cat_native_snake_first_cover_source K C S C1 t T T0 P Q A B X D b c h) (@kernel_adjunction_family_func
    K C S t T P (@transf_arrow_diagram_func K C (@one_cat_native_snake_image_func K C S C1 t T T0 P Q A B X D b
    c h) (@kernel_adjunction_family_func K C S t T P (@transf_arrow_diagram_func K C X D c))
    (@one_cat_native_snake_image_lift K C S C1 t T T0 P Q A B X D b c h))) (@one_cat_native_snake_image_func K C
    S C1 t T T0 P Q A B X D b c h) (@kernel_adjunction_family_inclusion_transf K C S t T P
    (@transf_arrow_diagram_func K C (@one_cat_native_snake_image_func K C S C1 t T T0 P Q A B X D b c h)
    (@kernel_adjunction_family_func K C S t T P (@transf_arrow_diagram_func K C X D c))
    (@one_cat_native_snake_image_lift K C S C1 t T T0 P Q A B X D b c h)))
    (@one_cat_native_snake_first_cover_transf K C S C1 t T T0 P Q A B X D b c h)) (@comp_fapp0 (Functor_cat K C)
    (@one_cat_native_snake_first_cover_source K C S C1 t T T0 P Q A B X D b c h) A
    (@one_cat_native_snake_image_func K C S C1 t T T0 P Q A B X D b c h) (@one_cat_native_snake_source_image K C
    S C1 t T T0 P Q A B X D b c h) (@one_cat_native_snake_first_cover_first K C S C1 t T T0 P Q A B X D b c h)))
≔ (@one_cat_kernel_precomposition_square_path K C S C1 t T T0 P A (@transf_arrow_diagram_func K C
  (@one_cat_native_snake_image_func K C S C1 t T T0 P Q A B X D b c h) (@kernel_adjunction_family_func K C S t T
  P (@transf_arrow_diagram_func K C X D c)) (@one_cat_native_snake_image_lift K C S C1 t T T0 P Q A B X D b c
  h)) (@one_cat_native_snake_source_image K C S C1 t T T0 P Q A B X D b c h));

// The original α kills j_L because v s_a=α.
symbol one_cat_native_snake_first_cover_alpha_zero [K C : Cat] [S : τ (@PreadditiveCategory C)]
  (C1 : τ (IsNCat (cat_succ cat_zero) C)) [t : τ (Obj C)]
  (T : τ (@TerminalObject C t)) (T0 : τ (@TerminalObject (Op_cat C) t))
  (P : τ (@KernelAdjunctionStructure C S t T)) (Q : τ (@CokernelAdjunctionStructure C S t T0))
  [A B X D : τ (Functor K C)] (b : τ (@Transf K C B X)) (c : τ (@Transf K C X D))
  (h : τ (@NativeSnakeInput K C t T A B X D b c))
  : τ (@= (@Transf K C (@one_cat_native_snake_first_cover_source K C S C1 t T T0 P Q A B X D b c h)
    (@kernel_adjunction_family_func K C S t T P (@transf_arrow_diagram_func K C X D c))) (@comp_fapp0
    (Functor_cat K C) (@one_cat_native_snake_first_cover_source K C S C1 t T T0 P Q A B X D b c h) A
    (@kernel_adjunction_family_func K C S t T P (@transf_arrow_diagram_func K C X D c))
    (@one_cat_native_snake_alpha K C S C1 t T T0 P A B X D b c h) (@one_cat_native_snake_first_cover_first K C S
    C1 t T T0 P Q A B X D b c h)) (@zero_arrow_family_zero_transf K C t T T0
    (@one_cat_native_snake_first_cover_source K C S C1 t T T0 P Q A B X D b c h) (@kernel_adjunction_family_func
    K C S t T P (@transf_arrow_diagram_func K C X D c))))
≔ (@eq_trans _ _ _ _ (@eq_ap (@Transf K C A (@kernel_adjunction_family_func K C S t T P
  (@transf_arrow_diagram_func K C X D c))) (@Transf K C (@one_cat_native_snake_first_cover_source K C S C1 t T
  T0 P Q A B X D b c h) (@kernel_adjunction_family_func K C S t T P (@transf_arrow_diagram_func K C X D c))) (λ
  v : τ (@Transf K C A (@kernel_adjunction_family_func K C S t T P (@transf_arrow_diagram_func K C X D c))),
  (@comp_fapp0 (Functor_cat K C) (@one_cat_native_snake_first_cover_source K C S C1 t T T0 P Q A B X D b c h) A
  (@kernel_adjunction_family_func K C S t T P (@transf_arrow_diagram_func K C X D c)) v
  (@one_cat_native_snake_first_cover_first K C S C1 t T T0 P Q A B X D b c h))) _ _ (@eq_sym _ _ _
  (@one_cat_native_snake_image_lift_source_path K C S C1 t T T0 P Q A B X D b c h)))
  (@one_cat_kernel_family_annihilation_path K C S C1 t T T0 P (@precomposed_diagram_family_func K C A
  (@transf_arrow_diagram_func K C (@one_cat_native_snake_image_func K C S C1 t T T0 P Q A B X D b c h)
  (@kernel_adjunction_family_func K C S t T P (@transf_arrow_diagram_func K C X D c))
  (@one_cat_native_snake_image_lift K C S C1 t T T0 P Q A B X D b c h)) (@one_cat_native_snake_source_image K C
  S C1 t T T0 P Q A B X D b c h))));

// Native lifting gives the required map L⇒K(α).
symbol one_cat_native_snake_first_cover_to_alpha_kernel [K C : Cat] [S : τ (@PreadditiveCategory C)]
  (C1 : τ (IsNCat (cat_succ cat_zero) C)) [t : τ (Obj C)]
  (T : τ (@TerminalObject C t)) (T0 : τ (@TerminalObject (Op_cat C) t))
  (P : τ (@KernelAdjunctionStructure C S t T)) (Q : τ (@CokernelAdjunctionStructure C S t T0))
  [A B X D : τ (Functor K C)] (b : τ (@Transf K C B X)) (c : τ (@Transf K C X D))
  (h : τ (@NativeSnakeInput K C t T A B X D b c))
  : τ (@Transf K C (@one_cat_native_snake_first_cover_source K C S C1 t T T0 P Q A B X D b c h)
    (@kernel_adjunction_family_func K C S t T P (@one_cat_native_snake_alpha_diagram K C S C1 t T T0 P A B X D b
    c h)))
≔ (@one_cat_kernel_family_lift K C S C1 t T T0 P (@one_cat_native_snake_first_cover_source K C S C1 t T T0 P Q A
  B X D b c h) (@one_cat_native_snake_alpha_diagram K C S C1 t T T0 P A B X D b c h)
  (@one_cat_native_snake_first_cover_first K C S C1 t T T0 P Q A B X D b c h)
  (@one_cat_native_snake_first_cover_alpha_zero K C S C1 t T T0 P Q A B X D b c h));

// Its original inclusion recovers j_L.
symbol one_cat_native_snake_first_cover_alpha_reconstruction [K C : Cat] [S : τ (@PreadditiveCategory C)]
  (C1 : τ (IsNCat (cat_succ cat_zero) C)) [t : τ (Obj C)]
  (T : τ (@TerminalObject C t)) (T0 : τ (@TerminalObject (Op_cat C) t))
  (P : τ (@KernelAdjunctionStructure C S t T)) (Q : τ (@CokernelAdjunctionStructure C S t T0))
  [A B X D : τ (Functor K C)] (b : τ (@Transf K C B X)) (c : τ (@Transf K C X D))
  (h : τ (@NativeSnakeInput K C t T A B X D b c))
  : τ (@= (@Transf K C (@one_cat_native_snake_first_cover_source K C S C1 t T T0 P Q A B X D b c h) A)
    (@comp_fapp0 (Functor_cat K C) (@one_cat_native_snake_first_cover_source K C S C1 t T T0 P Q A B X D b c h)
    (@kernel_adjunction_family_func K C S t T P (@one_cat_native_snake_alpha_diagram K C S C1 t T T0 P A B X D b
    c h)) A (@kernel_adjunction_family_inclusion_transf K C S t T P (@one_cat_native_snake_alpha_diagram K C S
    C1 t T T0 P A B X D b c h)) (@one_cat_native_snake_first_cover_to_alpha_kernel K C S C1 t T T0 P Q A B X D b
    c h)) (@one_cat_native_snake_first_cover_first K C S C1 t T T0 P Q A B X D b c h))
≔ (@one_cat_kernel_family_lift_ambient_reconstruction K C S C1 t T T0 P
  (@one_cat_native_snake_first_cover_source K C S C1 t T T0 P Q A B X D b c h)
  (@one_cat_native_snake_alpha_diagram K C S C1 t T T0 P A B X D b c h) (@one_cat_native_snake_first_cover_first
  K C S C1 t T T0 P Q A B X D b c h) (@one_cat_native_snake_first_cover_alpha_zero K C S C1 t T T0 P Q A B X D b
  c h));

// The original derived cover r_L cancels whole maps out of K(v).
symbol one_cat_native_snake_first_cover_reflect_path [K C : Cat]
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
  : τ (@= (@Transf K C (@kernel_adjunction_family_func K C (@additive_preadditive C Prod t Add) t
    (@additive_terminal_object C Prod t Add) P (@transf_arrow_diagram_func K C (@one_cat_native_snake_image_func
    K C (@additive_preadditive C Prod t Add) C1 t (@additive_terminal_object C Prod t Add) T0 P Q A B X D b c h)
    (@kernel_adjunction_family_func K C (@additive_preadditive C Prod t Add) t (@additive_terminal_object C Prod
    t Add) P (@transf_arrow_diagram_func K C X D c)) (@one_cat_native_snake_image_lift K C
    (@additive_preadditive C Prod t Add) C1 t (@additive_terminal_object C Prod t Add) T0 P Q A B X D b c h)))
    Y) u w)
≔ @one_cat_kernel_precomposition_reflect_path K C C1 Prod t Add T0 P Q N A (@transf_arrow_diagram_func K C
  (@one_cat_native_snake_image_func K C (@additive_preadditive C Prod t Add) C1 t (@additive_terminal_object C
  Prod t Add) T0 P Q A B X D b c h) (@kernel_adjunction_family_func K C (@additive_preadditive C Prod t Add) t
  (@additive_terminal_object C Prod t Add) P (@transf_arrow_diagram_func K C X D c))
  (@one_cat_native_snake_image_lift K C (@additive_preadditive C Prod t Add) C1 t (@additive_terminal_object C
  Prod t Add) T0 P Q A B X D b c h)) (@one_cat_native_snake_source_image K C (@additive_preadditive C Prod t
  Add) C1 t (@additive_terminal_object C Prod t Add) T0 P Q A B X D b c h)
  (@one_cat_native_snake_image_source_cokernel_zero K C (@additive_preadditive C Prod t Add) C1 t
  (@additive_terminal_object C Prod t Add) T0 P Q N A B X D b c h) Y u w p;
