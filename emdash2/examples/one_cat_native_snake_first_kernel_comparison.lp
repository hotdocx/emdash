/* Original whole representatives and canonical first-position exactness. */
require open emdash.emdash3_2_one_cat_native_snake_first_kernel_comparison;

assert [K C : Cat] [S : τ (@PreadditiveCategory C)]
  (C1 : τ (IsNCat (cat_succ cat_zero) C)) [t : τ (Obj C)]
  (T : τ (@TerminalObject C t)) (T0 : τ (@TerminalObject (Op_cat C) t))
  (P : τ (@KernelAdjunctionStructure C S t T)) (Q : τ (@CokernelAdjunctionStructure C S t T0))
  [A B X D : τ (Functor K C)] (b : τ (@Transf K C B X)) (c : τ (@Transf K C X D))
  (h : τ (@NativeSnakeInput K C t T A B X D b c))
  ⊢ @one_cat_native_snake_first_kernel_image_reconstruction K C S C1 t T T0 P Q A B X D b c h
  : τ (@= (@Transf K C (@kernel_adjunction_family_func K C S t T P (@transf_arrow_diagram_func K C
    (@kernel_adjunction_family_func K C S t T P (@transf_arrow_diagram_func K C B X b))
    (@kernel_adjunction_family_func K C S t T P (@one_cat_native_snake_gamma_diagram K C S C1 t T T0 Q A B X D b
    c h)) (@one_cat_native_snake_kernel_second K C S C1 t T T0 P Q A B X D b c h))) B) (@comp_fapp0 (Functor_cat
    K C) (@kernel_adjunction_family_func K C S t T P (@transf_arrow_diagram_func K C
    (@kernel_adjunction_family_func K C S t T P (@transf_arrow_diagram_func K C B X b))
    (@kernel_adjunction_family_func K C S t T P (@one_cat_native_snake_gamma_diagram K C S C1 t T T0 Q A B X D b
    c h)) (@one_cat_native_snake_kernel_second K C S C1 t T T0 P Q A B X D b c h)))
    (@one_cat_native_snake_image_func K C S C1 t T T0 P Q A B X D b c h) B
    (@one_cat_native_snake_image_inclusion K C S C1 t T T0 P Q A B X D b c h)
    (@one_cat_native_snake_first_kernel_image_lift K C S C1 t T T0 P Q A B X D b c h)) (@comp_fapp0 (Functor_cat
    K C) (@kernel_adjunction_family_func K C S t T P (@transf_arrow_diagram_func K C
    (@kernel_adjunction_family_func K C S t T P (@transf_arrow_diagram_func K C B X b))
    (@kernel_adjunction_family_func K C S t T P (@one_cat_native_snake_gamma_diagram K C S C1 t T T0 Q A B X D b
    c h)) (@one_cat_native_snake_kernel_second K C S C1 t T T0 P Q A B X D b c h)))
    (@kernel_adjunction_family_func K C S t T P (@transf_arrow_diagram_func K C B X b)) B
    (@kernel_adjunction_family_inclusion_transf K C S t T P (@transf_arrow_diagram_func K C B X b))
    (@kernel_adjunction_family_inclusion_transf K C S t T P (@transf_arrow_diagram_func K C
    (@kernel_adjunction_family_func K C S t T P (@transf_arrow_diagram_func K C B X b))
    (@kernel_adjunction_family_func K C S t T P (@one_cat_native_snake_gamma_diagram K C S C1 t T T0 Q A B X D b
    c h)) (@one_cat_native_snake_kernel_second K C S C1 t T T0 P Q A B X D b c h)))));

assert [K C : Cat] [S : τ (@PreadditiveCategory C)]
  (C1 : τ (IsNCat (cat_succ cat_zero) C)) [t : τ (Obj C)]
  (T : τ (@TerminalObject C t)) (T0 : τ (@TerminalObject (Op_cat C) t))
  (P : τ (@KernelAdjunctionStructure C S t T)) (Q : τ (@CokernelAdjunctionStructure C S t T0))
  [A B X D : τ (Functor K C)] (b : τ (@Transf K C B X)) (c : τ (@Transf K C X D))
  (h : τ (@NativeSnakeInput K C t T A B X D b c))
  ⊢ @one_cat_native_snake_first_kernel_to_image_kernel_reconstruction K C S C1 t T T0 P Q A B X D b c h
  : τ (@= (@Transf K C (@kernel_adjunction_family_func K C S t T P (@transf_arrow_diagram_func K C
    (@kernel_adjunction_family_func K C S t T P (@transf_arrow_diagram_func K C B X b))
    (@kernel_adjunction_family_func K C S t T P (@one_cat_native_snake_gamma_diagram K C S C1 t T T0 Q A B X D b
    c h)) (@one_cat_native_snake_kernel_second K C S C1 t T T0 P Q A B X D b c h)))
    (@one_cat_native_snake_image_func K C S C1 t T T0 P Q A B X D b c h)) (@comp_fapp0 (Functor_cat K C)
    (@kernel_adjunction_family_func K C S t T P (@transf_arrow_diagram_func K C (@kernel_adjunction_family_func
    K C S t T P (@transf_arrow_diagram_func K C B X b)) (@kernel_adjunction_family_func K C S t T P
    (@one_cat_native_snake_gamma_diagram K C S C1 t T T0 Q A B X D b c h)) (@one_cat_native_snake_kernel_second
    K C S C1 t T T0 P Q A B X D b c h))) (@kernel_adjunction_family_func K C S t T P (@transf_arrow_diagram_func
    K C (@one_cat_native_snake_image_func K C S C1 t T T0 P Q A B X D b c h) (@kernel_adjunction_family_func K C
    S t T P (@transf_arrow_diagram_func K C X D c)) (@one_cat_native_snake_image_lift K C S C1 t T T0 P Q A B X
    D b c h))) (@one_cat_native_snake_image_func K C S C1 t T T0 P Q A B X D b c h)
    (@kernel_adjunction_family_inclusion_transf K C S t T P (@transf_arrow_diagram_func K C
    (@one_cat_native_snake_image_func K C S C1 t T T0 P Q A B X D b c h) (@kernel_adjunction_family_func K C S t
    T P (@transf_arrow_diagram_func K C X D c)) (@one_cat_native_snake_image_lift K C S C1 t T T0 P Q A B X D b
    c h))) (@one_cat_native_snake_first_kernel_to_image_kernel K C S C1 t T T0 P Q A B X D b c h))
    (@one_cat_native_snake_first_kernel_image_lift K C S C1 t T T0 P Q A B X D b c h));

assert [K C : Cat] [S : τ (@PreadditiveCategory C)]
  (C1 : τ (IsNCat (cat_succ cat_zero) C)) [t : τ (Obj C)]
  (T : τ (@TerminalObject C t)) (T0 : τ (@TerminalObject (Op_cat C) t))
  (P : τ (@KernelAdjunctionStructure C S t T)) (Q : τ (@CokernelAdjunctionStructure C S t T0))
  [A B X D : τ (Functor K C)] (b : τ (@Transf K C B X)) (c : τ (@Transf K C X D))
  (h : τ (@NativeSnakeInput K C t T A B X D b c))
  ⊢ @one_cat_native_snake_first_image_kernel_kernel_reconstruction K C S C1 t T T0 P Q A B X D b c h
  : τ (@= (@Transf K C (@kernel_adjunction_family_func K C S t T P (@transf_arrow_diagram_func K C
    (@one_cat_native_snake_image_func K C S C1 t T T0 P Q A B X D b c h) (@kernel_adjunction_family_func K C S t
    T P (@transf_arrow_diagram_func K C X D c)) (@one_cat_native_snake_image_lift K C S C1 t T T0 P Q A B X D b
    c h))) (@kernel_adjunction_family_func K C S t T P (@transf_arrow_diagram_func K C B X b))) (@comp_fapp0
    (Functor_cat K C) (@kernel_adjunction_family_func K C S t T P (@transf_arrow_diagram_func K C
    (@one_cat_native_snake_image_func K C S C1 t T T0 P Q A B X D b c h) (@kernel_adjunction_family_func K C S t
    T P (@transf_arrow_diagram_func K C X D c)) (@one_cat_native_snake_image_lift K C S C1 t T T0 P Q A B X D b
    c h))) (@kernel_adjunction_family_func K C S t T P (@transf_arrow_diagram_func K C
    (@kernel_adjunction_family_func K C S t T P (@transf_arrow_diagram_func K C B X b))
    (@kernel_adjunction_family_func K C S t T P (@one_cat_native_snake_gamma_diagram K C S C1 t T T0 Q A B X D b
    c h)) (@one_cat_native_snake_kernel_second K C S C1 t T T0 P Q A B X D b c h)))
    (@kernel_adjunction_family_func K C S t T P (@transf_arrow_diagram_func K C B X b))
    (@kernel_adjunction_family_inclusion_transf K C S t T P (@transf_arrow_diagram_func K C
    (@kernel_adjunction_family_func K C S t T P (@transf_arrow_diagram_func K C B X b))
    (@kernel_adjunction_family_func K C S t T P (@one_cat_native_snake_gamma_diagram K C S C1 t T T0 Q A B X D b
    c h)) (@one_cat_native_snake_kernel_second K C S C1 t T T0 P Q A B X D b c h)))
    (@one_cat_native_snake_first_image_kernel_to_kernel K C S C1 t T T0 P Q A B X D b c h))
    (@one_cat_native_snake_first_image_kernel_to_middle K C S C1 t T T0 P Q A B X D b c h));

assert [K C : Cat] [S : τ (@PreadditiveCategory C)]
  (C1 : τ (IsNCat (cat_succ cat_zero) C)) [t : τ (Obj C)]
  (T : τ (@TerminalObject C t)) (T0 : τ (@TerminalObject (Op_cat C) t))
  (P : τ (@KernelAdjunctionStructure C S t T)) (Q : τ (@CokernelAdjunctionStructure C S t T0))
  [A B X D : τ (Functor K C)] (b : τ (@Transf K C B X)) (c : τ (@Transf K C X D))
  (h : τ (@NativeSnakeInput K C t T A B X D b c))
  ⊢ @one_cat_native_snake_first_kernel_retraction_path K C S C1 t T T0 P Q A B X D b c h
  : τ (@= (@Transf K C (@kernel_adjunction_family_func K C S t T P (@transf_arrow_diagram_func K C
    (@kernel_adjunction_family_func K C S t T P (@transf_arrow_diagram_func K C B X b))
    (@kernel_adjunction_family_func K C S t T P (@one_cat_native_snake_gamma_diagram K C S C1 t T T0 Q A B X D b
    c h)) (@one_cat_native_snake_kernel_second K C S C1 t T T0 P Q A B X D b c h)))
    (@kernel_adjunction_family_func K C S t T P (@transf_arrow_diagram_func K C (@kernel_adjunction_family_func
    K C S t T P (@transf_arrow_diagram_func K C B X b)) (@kernel_adjunction_family_func K C S t T P
    (@one_cat_native_snake_gamma_diagram K C S C1 t T T0 Q A B X D b c h)) (@one_cat_native_snake_kernel_second
    K C S C1 t T T0 P Q A B X D b c h)))) (@comp_fapp0 (Functor_cat K C) (@kernel_adjunction_family_func K C S t
    T P (@transf_arrow_diagram_func K C (@kernel_adjunction_family_func K C S t T P (@transf_arrow_diagram_func
    K C B X b)) (@kernel_adjunction_family_func K C S t T P (@one_cat_native_snake_gamma_diagram K C S C1 t T T0
    Q A B X D b c h)) (@one_cat_native_snake_kernel_second K C S C1 t T T0 P Q A B X D b c h)))
    (@kernel_adjunction_family_func K C S t T P (@transf_arrow_diagram_func K C
    (@one_cat_native_snake_image_func K C S C1 t T T0 P Q A B X D b c h) (@kernel_adjunction_family_func K C S t
    T P (@transf_arrow_diagram_func K C X D c)) (@one_cat_native_snake_image_lift K C S C1 t T T0 P Q A B X D b
    c h))) (@kernel_adjunction_family_func K C S t T P (@transf_arrow_diagram_func K C
    (@kernel_adjunction_family_func K C S t T P (@transf_arrow_diagram_func K C B X b))
    (@kernel_adjunction_family_func K C S t T P (@one_cat_native_snake_gamma_diagram K C S C1 t T T0 Q A B X D b
    c h)) (@one_cat_native_snake_kernel_second K C S C1 t T T0 P Q A B X D b c h)))
    (@one_cat_native_snake_first_image_kernel_to_kernel K C S C1 t T T0 P Q A B X D b c h)
    (@one_cat_native_snake_first_kernel_to_image_kernel K C S C1 t T T0 P Q A B X D b c h)) (@id (Functor_cat K
    C) (@kernel_adjunction_family_func K C S t T P (@transf_arrow_diagram_func K C
    (@kernel_adjunction_family_func K C S t T P (@transf_arrow_diagram_func K C B X b))
    (@kernel_adjunction_family_func K C S t T P (@one_cat_native_snake_gamma_diagram K C S C1 t T T0 Q A B X D b
    c h)) (@one_cat_native_snake_kernel_second K C S C1 t T T0 P Q A B X D b c h)))));
