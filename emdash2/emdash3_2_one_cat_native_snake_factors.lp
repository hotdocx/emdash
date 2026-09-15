/* General whole snake factors α:A⇒K(c) and γ:Q(a)⇒D.
   Use the original adjunction mates and their whole reconstruction laws. */
require open emdash.emdash3_2_native_snake_inputs;
require open emdash.emdash3_2_one_cat_short_exact_family_cancellation;
require open emdash.emdash3_2_one_cat_kernel_family_reconstruction;
require open emdash.emdash3_2_cokernel_adjunction_families;

// α:A⇒K(c) from the original whole kernel mate.
symbol one_cat_native_snake_alpha [K C : Cat] [S : τ (@PreadditiveCategory C)]
  (C1 : τ (IsNCat (cat_succ cat_zero) C)) [t : τ (Obj C)]
  (T : τ (@TerminalObject C t)) (T0 : τ (@TerminalObject (Op_cat C) t))
  (P : τ (@KernelAdjunctionStructure C S t T))
  [A B X D : τ (Functor K C)] (b : τ (@Transf K C B X)) (c : τ (@Transf K C X D))
  (h : τ (@NativeSnakeInput K C t T A B X D b c))
  : τ (@Transf K C A (@kernel_adjunction_family_func K C S t T P (@transf_arrow_diagram_func K C X D c)))
≔ @one_cat_kernel_family_lift K C S C1 t T T0 P A (@transf_arrow_diagram_func K C X D c)
    (@comp_fapp0 (Functor_cat K C) A B X b (@native_snake_incoming K C t T A B X D b c h))
    (@one_cat_native_snake_zero K C C1 t T T0 A B X D b c h);

// γ:Q(a)⇒D from the original whole cokernel mate, at Arr(a) itself.
symbol one_cat_native_snake_gamma [K C : Cat] [S : τ (@PreadditiveCategory C)]
  (C1 : τ (IsNCat (cat_succ cat_zero) C)) [t : τ (Obj C)]
  (T : τ (@TerminalObject C t)) (T0 : τ (@TerminalObject (Op_cat C) t))
  (Q : τ (@CokernelAdjunctionStructure C S t T0))
  [A B X D : τ (Functor K C)] (b : τ (@Transf K C B X)) (c : τ (@Transf K C X D))
  (h : τ (@NativeSnakeInput K C t T A B X D b c))
  : τ (@Transf K C (@cokernel_adjunction_family_func K C S t T0 Q
      (@native_snake_incoming_diagram K C t T A B X D b c h)) D)
≔ @one_cat_row_cokernel_comparison K C S C1 t T T0 Q A
    (@transf_arrow_diagram_func K C B D (@comp_fapp0 (Functor_cat K C) B X D c b)) h;

// Native reconstruction fixes the original b∘a and hence the factor's sign.
symbol one_cat_native_snake_alpha_reconstruction [K C : Cat] [S : τ (@PreadditiveCategory C)]
  (C1 : τ (IsNCat (cat_succ cat_zero) C)) [t : τ (Obj C)]
  (T : τ (@TerminalObject C t)) (T0 : τ (@TerminalObject (Op_cat C) t))
  (P : τ (@KernelAdjunctionStructure C S t T))
  [A B X D : τ (Functor K C)] (b : τ (@Transf K C B X)) (c : τ (@Transf K C X D))
  (h : τ (@NativeSnakeInput K C t T A B X D b c))
  : τ (@= (@Transf K C A X)
      (@comp_fapp0 (Functor_cat K C) A
        (@kernel_adjunction_family_func K C S t T P (@transf_arrow_diagram_func K C X D c)) X
        (@kernel_adjunction_family_inclusion_transf K C S t T P (@transf_arrow_diagram_func K C X D c))
        (@one_cat_native_snake_alpha K C S C1 t T T0 P A B X D b c h))
      (@comp_fapp0 (Functor_cat K C) A B X b (@native_snake_incoming K C t T A B X D b c h)))
≔ @one_cat_kernel_family_lift_ambient_reconstruction K C S C1 t T T0 P A
    (@transf_arrow_diagram_func K C X D c)
    (@comp_fapp0 (Functor_cat K C) A B X b (@native_snake_incoming K C t T A B X D b c h))
    (@one_cat_native_snake_zero K C C1 t T T0 A B X D b c h);

// The same original quotient reconstructs c∘b, without a second choice.
symbol one_cat_native_snake_gamma_reconstruction [K C : Cat] [S : τ (@PreadditiveCategory C)]
  (C1 : τ (IsNCat (cat_succ cat_zero) C)) [t : τ (Obj C)]
  (T : τ (@TerminalObject C t)) (T0 : τ (@TerminalObject (Op_cat C) t))
  (Q : τ (@CokernelAdjunctionStructure C S t T0))
  [A B X D : τ (Functor K C)] (b : τ (@Transf K C B X)) (c : τ (@Transf K C X D))
  (h : τ (@NativeSnakeInput K C t T A B X D b c))
  : τ (@= (@Transf K C B D)
      (@comp_fapp0 (Functor_cat K C) B
        (@cokernel_adjunction_family_func K C S t T0 Q (@native_snake_incoming_diagram K C t T A B X D b c h)) D
        (@one_cat_native_snake_gamma K C S C1 t T T0 Q A B X D b c h)
        (@cokernel_adjunction_family_projection_transf K C S t T0 Q (@native_snake_incoming_diagram K C t T A B X D b c h)))
      (@comp_fapp0 (Functor_cat K C) B X D c b))
≔ @one_cat_row_cokernel_ambient_reconstruction_path K C S C1 t T T0 Q A
    (@transf_arrow_diagram_func K C B D (@comp_fapp0 (Functor_cat K C) B X D c b)) h;
