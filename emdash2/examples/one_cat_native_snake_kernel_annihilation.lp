/* Native factorization of the actual restricted covered map through the original image. */
require open emdash.emdash3_2_one_cat_native_snake_kernel_annihilation;

assert [K C : Cat] [S : τ (@PreadditiveCategory C)]
  (C1 : τ (IsNCat (cat_succ cat_zero) C)) [t : τ (Obj C)]
  (T : τ (@TerminalObject C t)) (T0 : τ (@TerminalObject (Op_cat C) t))
  (P : τ (@KernelAdjunctionStructure C S t T)) (Q : τ (@CokernelAdjunctionStructure C S t T0))
  [A B X D : τ (Functor K C)] (b : τ (@Transf K C B X)) (c : τ (@Transf K C X D))
  (h : τ (@NativeSnakeInput K C t T A B X D b c))
  ⊢ @one_cat_native_snake_image_lift_source_path K C S C1 t T T0 P Q A B X D b c h
  : τ(@= (@Transf K C A (@kernel_adjunction_family_func K C S t T P (@transf_arrow_diagram_func K C X D c)))
    (@comp_fapp0 (Functor_cat K C) A (@one_cat_native_snake_image_func K C S C1 t T T0 P Q A B X D b c h)
    (@kernel_adjunction_family_func K C S t T P (@transf_arrow_diagram_func K C X D c))
    (@one_cat_native_snake_image_lift K C S C1 t T T0 P Q A B X D b c h) (@one_cat_native_snake_source_image K C
    S C1 t T T0 P Q A B X D b c h)) (@one_cat_native_snake_alpha K C S C1 t T T0 P A B X D b c h));

assert [K C : Cat] [S : τ (@PreadditiveCategory C)]
  (C1 : τ (IsNCat (cat_succ cat_zero) C)) [t : τ (Obj C)]
  (T : τ (@TerminalObject C t)) (T0 : τ (@TerminalObject (Op_cat C) t))
  (P : τ (@KernelAdjunctionStructure C S t T)) (Q : τ (@CokernelAdjunctionStructure C S t T0))
  (N : τ (@OneCatAdjunctionNormality C S C1 t T T0 P Q))
  [A B X D : τ (Functor K C)] (b : τ (@Transf K C B X)) (c : τ (@Transf K C X D))
  (h : τ (@NativeSnakeInput K C t T A B X D b c))
  ⊢ @one_cat_native_snake_image_quotient_zero K C S C1 t T T0 P Q N A B X D b c h
  : τ(@= (@Transf K C (@one_cat_native_snake_image_func K C S C1 t T T0 P Q A B X D b c h)
    (@cokernel_adjunction_family_func K C S t T0 Q (@one_cat_native_snake_alpha_diagram K C S C1 t T T0 P A B X
    D b c h))) (@comp_fapp0 (Functor_cat K C) (@one_cat_native_snake_image_func K C S C1 t T T0 P Q A B X D b c
    h) (@kernel_adjunction_family_func K C S t T P (@transf_arrow_diagram_func K C X D c))
    (@cokernel_adjunction_family_func K C S t T0 Q (@one_cat_native_snake_alpha_diagram K C S C1 t T T0 P A B X
    D b c h)) (@cokernel_adjunction_family_projection_transf K C S t T0 Q (@one_cat_native_snake_alpha_diagram K
    C S C1 t T T0 P A B X D b c h)) (@one_cat_native_snake_image_lift K C S C1 t T T0 P Q A B X D b c h))
    (@zero_arrow_family_zero_transf K C t T T0 (@one_cat_native_snake_image_func K C S C1 t T T0 P Q A B X D b c
    h) (@cokernel_adjunction_family_func K C S t T0 Q (@one_cat_native_snake_alpha_diagram K C S C1 t T T0 P A B
    X D b c h))));

assert [K C : Cat] [S : τ (@PreadditiveCategory C)]
  (C1 : τ (IsNCat (cat_succ cat_zero) C)) [t : τ (Obj C)]
  (T : τ (@TerminalObject C t)) (T0 : τ (@TerminalObject (Op_cat C) t))
  (P : τ (@KernelAdjunctionStructure C S t T)) (Q : τ (@CokernelAdjunctionStructure C S t T0))
  [A B X D : τ (Functor K C)] (b : τ (@Transf K C B X)) (c : τ (@Transf K C X D))
  (h : τ (@NativeSnakeInput K C t T A B X D b c))
  ⊢ @one_cat_native_snake_kernel_image_reconstruction K C S C1 t T T0 P Q A B X D b c h
  : τ(@= (@Transf K C (@kernel_adjunction_family_func K C S t T P (@transf_arrow_diagram_func K C
    (@one_cat_native_snake_cover_source K C S C1 t T T0 P Q A B X D b c h) (@kernel_adjunction_family_func K C S
    t T P (@one_cat_native_snake_gamma_diagram K C S C1 t T T0 Q A B X D b c h))
    (@one_cat_native_snake_cover_transf K C S C1 t T T0 P Q A B X D b c h))) B) (@comp_fapp0 (Functor_cat K C)
    (@kernel_adjunction_family_func K C S t T P (@transf_arrow_diagram_func K C
    (@one_cat_native_snake_cover_source K C S C1 t T T0 P Q A B X D b c h) (@kernel_adjunction_family_func K C S
    t T P (@one_cat_native_snake_gamma_diagram K C S C1 t T T0 Q A B X D b c h))
    (@one_cat_native_snake_cover_transf K C S C1 t T T0 P Q A B X D b c h))) (@one_cat_native_snake_image_func K
    C S C1 t T T0 P Q A B X D b c h) B (@one_cat_native_snake_image_inclusion K C S C1 t T T0 P Q A B X D b c h)
    (@one_cat_native_snake_kernel_image_lift K C S C1 t T T0 P Q A B X D b c h)) (@comp_fapp0 (Functor_cat K C)
    (@kernel_adjunction_family_func K C S t T P (@transf_arrow_diagram_func K C
    (@one_cat_native_snake_cover_source K C S C1 t T T0 P Q A B X D b c h) (@kernel_adjunction_family_func K C S
    t T P (@one_cat_native_snake_gamma_diagram K C S C1 t T T0 Q A B X D b c h))
    (@one_cat_native_snake_cover_transf K C S C1 t T T0 P Q A B X D b c h))) (@one_cat_native_snake_cover_source
    K C S C1 t T T0 P Q A B X D b c h) B (@one_cat_native_snake_cover_first K C S C1 t T T0 P Q A B X D b c h)
    (@kernel_adjunction_family_inclusion_transf K C S t T P (@transf_arrow_diagram_func K C
    (@one_cat_native_snake_cover_source K C S C1 t T T0 P Q A B X D b c h) (@kernel_adjunction_family_func K C S
    t T P (@one_cat_native_snake_gamma_diagram K C S C1 t T T0 Q A B X D b c h))
    (@one_cat_native_snake_cover_transf K C S C1 t T T0 P Q A B X D b c h)))));

assert [K C : Cat] [S : τ (@PreadditiveCategory C)]
  (C1 : τ (IsNCat (cat_succ cat_zero) C)) [t : τ (Obj C)]
  (T : τ (@TerminalObject C t)) (T0 : τ (@TerminalObject (Op_cat C) t))
  (P : τ (@KernelAdjunctionStructure C S t T)) (Q : τ (@CokernelAdjunctionStructure C S t T0))
  [A B X D : τ (Functor K C)] (b : τ (@Transf K C B X)) (c : τ (@Transf K C X D))
  (h : τ (@NativeSnakeInput K C t T A B X D b c))
  ⊢ @one_cat_native_snake_covered_kernel_factor_path K C S C1 t T T0 P Q A B X D b c h
  : τ(@= (@Transf K C (@kernel_adjunction_family_func K C S t T P (@transf_arrow_diagram_func K C
    (@one_cat_native_snake_cover_source K C S C1 t T T0 P Q A B X D b c h) (@kernel_adjunction_family_func K C S
    t T P (@one_cat_native_snake_gamma_diagram K C S C1 t T T0 Q A B X D b c h))
    (@one_cat_native_snake_cover_transf K C S C1 t T T0 P Q A B X D b c h))) (@kernel_adjunction_family_func K C
    S t T P (@transf_arrow_diagram_func K C X D c))) (@comp_fapp0 (Functor_cat K C)
    (@kernel_adjunction_family_func K C S t T P (@transf_arrow_diagram_func K C
    (@one_cat_native_snake_cover_source K C S C1 t T T0 P Q A B X D b c h) (@kernel_adjunction_family_func K C S
    t T P (@one_cat_native_snake_gamma_diagram K C S C1 t T T0 Q A B X D b c h))
    (@one_cat_native_snake_cover_transf K C S C1 t T T0 P Q A B X D b c h))) (@one_cat_native_snake_cover_source
    K C S C1 t T T0 P Q A B X D b c h) (@kernel_adjunction_family_func K C S t T P (@transf_arrow_diagram_func K
    C X D c)) (@one_cat_native_snake_covered_lift K C S C1 t T T0 P Q A B X D b c h)
    (@kernel_adjunction_family_inclusion_transf K C S t T P (@transf_arrow_diagram_func K C
    (@one_cat_native_snake_cover_source K C S C1 t T T0 P Q A B X D b c h) (@kernel_adjunction_family_func K C S
    t T P (@one_cat_native_snake_gamma_diagram K C S C1 t T T0 Q A B X D b c h))
    (@one_cat_native_snake_cover_transf K C S C1 t T T0 P Q A B X D b c h)))) (@comp_fapp0 (Functor_cat K C)
    (@kernel_adjunction_family_func K C S t T P (@transf_arrow_diagram_func K C
    (@one_cat_native_snake_cover_source K C S C1 t T T0 P Q A B X D b c h) (@kernel_adjunction_family_func K C S
    t T P (@one_cat_native_snake_gamma_diagram K C S C1 t T T0 Q A B X D b c h))
    (@one_cat_native_snake_cover_transf K C S C1 t T T0 P Q A B X D b c h))) (@one_cat_native_snake_image_func K
    C S C1 t T T0 P Q A B X D b c h) (@kernel_adjunction_family_func K C S t T P (@transf_arrow_diagram_func K C
    X D c)) (@one_cat_native_snake_image_lift K C S C1 t T T0 P Q A B X D b c h)
    (@one_cat_native_snake_kernel_image_lift K C S C1 t T T0 P Q A B X D b c h)));

assert [K C : Cat] [S : τ (@PreadditiveCategory C)]
  (C1 : τ (IsNCat (cat_succ cat_zero) C)) [t : τ (Obj C)]
  (T : τ (@TerminalObject C t)) (T0 : τ (@TerminalObject (Op_cat C) t))
  (P : τ (@KernelAdjunctionStructure C S t T)) (Q : τ (@CokernelAdjunctionStructure C S t T0))
  (N : τ (@OneCatAdjunctionNormality C S C1 t T T0 P Q))
  [A B X D : τ (Functor K C)] (b : τ (@Transf K C B X)) (c : τ (@Transf K C X D))
  (h : τ (@NativeSnakeInput K C t T A B X D b c))
  ⊢ @one_cat_native_snake_theta_kernel_zero K C S C1 t T T0 P Q N A B X D b c h
  : τ(@= (@Transf K C (@kernel_adjunction_family_func K C S t T P (@transf_arrow_diagram_func K C
    (@one_cat_native_snake_cover_source K C S C1 t T T0 P Q A B X D b c h) (@kernel_adjunction_family_func K C S
    t T P (@one_cat_native_snake_gamma_diagram K C S C1 t T T0 Q A B X D b c h))
    (@one_cat_native_snake_cover_transf K C S C1 t T T0 P Q A B X D b c h))) (@cokernel_adjunction_family_func K
    C S t T0 Q (@one_cat_native_snake_alpha_diagram K C S C1 t T T0 P A B X D b c h))) (@comp_fapp0 (Functor_cat
    K C) (@kernel_adjunction_family_func K C S t T P (@transf_arrow_diagram_func K C
    (@one_cat_native_snake_cover_source K C S C1 t T T0 P Q A B X D b c h) (@kernel_adjunction_family_func K C S
    t T P (@one_cat_native_snake_gamma_diagram K C S C1 t T T0 Q A B X D b c h))
    (@one_cat_native_snake_cover_transf K C S C1 t T T0 P Q A B X D b c h))) (@one_cat_native_snake_cover_source
    K C S C1 t T T0 P Q A B X D b c h) (@cokernel_adjunction_family_func K C S t T0 Q
    (@one_cat_native_snake_alpha_diagram K C S C1 t T T0 P A B X D b c h)) (@one_cat_native_snake_covered_transf
    K C S C1 t T T0 P Q A B X D b c h) (@kernel_adjunction_family_inclusion_transf K C S t T P
    (@transf_arrow_diagram_func K C (@one_cat_native_snake_cover_source K C S C1 t T T0 P Q A B X D b c h)
    (@kernel_adjunction_family_func K C S t T P (@one_cat_native_snake_gamma_diagram K C S C1 t T T0 Q A B X D b
    c h)) (@one_cat_native_snake_cover_transf K C S C1 t T T0 P Q A B X D b c h))))
    (@zero_arrow_family_zero_transf K C t T T0 (@kernel_adjunction_family_func K C S t T P
    (@transf_arrow_diagram_func K C (@one_cat_native_snake_cover_source K C S C1 t T T0 P Q A B X D b c h)
    (@kernel_adjunction_family_func K C S t T P (@one_cat_native_snake_gamma_diagram K C S C1 t T T0 Q A B X D b
    c h)) (@one_cat_native_snake_cover_transf K C S C1 t T T0 P Q A B X D b c h)))
    (@cokernel_adjunction_family_func K C S t T0 Q (@one_cat_native_snake_alpha_diagram K C S C1 t T T0 P A B X
    D b c h))));
