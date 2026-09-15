/* The positive whole covered snake map θ=π_α∘ℓ:E⇒Q(α).
   Annihilation on K(ρ) and descent to ∂ are subsequent obligations. */
require open emdash.emdash3_2_one_cat_native_snake_cover;

// c∘b kills the original inclusion E→B, by γ∘π_a=c∘b and kernel annihilation.
symbol one_cat_native_snake_covered_zero [K C : Cat] [S : τ (@PreadditiveCategory C)]
  (C1 : τ (IsNCat (cat_succ cat_zero) C)) [t : τ (Obj C)]
  (T : τ (@TerminalObject C t)) (T0 : τ (@TerminalObject (Op_cat C) t))
  (P : τ (@KernelAdjunctionStructure C S t T)) (Q : τ (@CokernelAdjunctionStructure C S t T0))
  [A B X D : τ (Functor K C)] (b : τ (@Transf K C B X)) (c : τ (@Transf K C X D))
  (h : τ (@NativeSnakeInput K C t T A B X D b c))
  : τ (@= (@Transf K C (@one_cat_native_snake_cover_source K C S C1 t T T0 P Q A B X D b c h) D)
      (@comp_fapp0 (Functor_cat K C) (@one_cat_native_snake_cover_source K C S C1 t T T0 P Q A B X D b c h) X D c
        (@comp_fapp0 (Functor_cat K C) (@one_cat_native_snake_cover_source K C S C1 t T T0 P Q A B X D b c h) B X b
          (@one_cat_native_snake_cover_first K C S C1 t T T0 P Q A B X D b c h)))
      (@zero_arrow_family_zero_transf K C t T T0 (@one_cat_native_snake_cover_source K C S C1 t T T0 P Q A B X D b c h) D))
≔ @eq_trans _ _ _ _
    (@comp_assoc (Functor_cat K C) (@one_cat_native_snake_cover_source K C S C1 t T T0 P Q A B X D b c h) B X D c b
      (@one_cat_native_snake_cover_first K C S C1 t T T0 P Q A B X D b c h))
    (@eq_trans _ _ _ _
      (@eq_ap (@Transf K C B D) (@Transf K C (@one_cat_native_snake_cover_source K C S C1 t T T0 P Q A B X D b c h) D)
        (λ v : τ (@Transf K C B D), @comp_fapp0 (Functor_cat K C)
          (@one_cat_native_snake_cover_source K C S C1 t T T0 P Q A B X D b c h) B D v
          (@one_cat_native_snake_cover_first K C S C1 t T T0 P Q A B X D b c h)) _ _
        (@eq_sym _ _ _ (@one_cat_native_snake_gamma_reconstruction K C S C1 t T T0 Q A B X D b c h)))
      (@one_cat_kernel_family_annihilation_path K C S C1 t T T0 P
        (@precomposed_diagram_family_func K C B
          (@one_cat_native_snake_gamma_diagram K C S C1 t T T0 Q A B X D b c h)
          (@native_snake_quotient_transf K C S t T T0 Q A B X D b c h))));

// ℓ:E⇒K(c) is the original whole kernel lift of b∘κ_E.
symbol one_cat_native_snake_covered_lift [K C : Cat] [S : τ (@PreadditiveCategory C)]
  (C1 : τ (IsNCat (cat_succ cat_zero) C)) [t : τ (Obj C)]
  (T : τ (@TerminalObject C t)) (T0 : τ (@TerminalObject (Op_cat C) t))
  (P : τ (@KernelAdjunctionStructure C S t T)) (Q : τ (@CokernelAdjunctionStructure C S t T0))
  [A B X D : τ (Functor K C)] (b : τ (@Transf K C B X)) (c : τ (@Transf K C X D))
  (h : τ (@NativeSnakeInput K C t T A B X D b c))
  : τ (@Transf K C (@one_cat_native_snake_cover_source K C S C1 t T T0 P Q A B X D b c h)
      (@kernel_adjunction_family_func K C S t T P (@transf_arrow_diagram_func K C X D c)))
≔ @one_cat_kernel_family_lift K C S C1 t T T0 P
    (@one_cat_native_snake_cover_source K C S C1 t T T0 P Q A B X D b c h) (@transf_arrow_diagram_func K C X D c)
    (@comp_fapp0 (Functor_cat K C) (@one_cat_native_snake_cover_source K C S C1 t T T0 P Q A B X D b c h) B X b
      (@one_cat_native_snake_cover_first K C S C1 t T T0 P Q A B X D b c h))
    (@one_cat_native_snake_covered_zero K C S C1 t T T0 P Q A B X D b c h);

// Whole reconstruction: κ_c∘ℓ=b∘κ_E, at the original K(c).
symbol one_cat_native_snake_covered_lift_reconstruction [K C : Cat] [S : τ (@PreadditiveCategory C)]
  (C1 : τ (IsNCat (cat_succ cat_zero) C)) [t : τ (Obj C)]
  (T : τ (@TerminalObject C t)) (T0 : τ (@TerminalObject (Op_cat C) t))
  (P : τ (@KernelAdjunctionStructure C S t T)) (Q : τ (@CokernelAdjunctionStructure C S t T0))
  [A B X D : τ (Functor K C)] (b : τ (@Transf K C B X)) (c : τ (@Transf K C X D))
  (h : τ (@NativeSnakeInput K C t T A B X D b c))
≔ @one_cat_kernel_family_lift_ambient_reconstruction K C S C1 t T T0 P
    (@one_cat_native_snake_cover_source K C S C1 t T T0 P Q A B X D b c h) (@transf_arrow_diagram_func K C X D c)
    (@comp_fapp0 (Functor_cat K C) (@one_cat_native_snake_cover_source K C S C1 t T T0 P Q A B X D b c h) B X b
      (@one_cat_native_snake_cover_first K C S C1 t T T0 P Q A B X D b c h))
    (@one_cat_native_snake_covered_zero K C S C1 t T T0 P Q A B X D b c h);

// The original whole α as an input to Q.
symbol one_cat_native_snake_alpha_diagram [K C : Cat] [S : τ (@PreadditiveCategory C)]
  (C1 : τ (IsNCat (cat_succ cat_zero) C)) [t : τ (Obj C)]
  (T : τ (@TerminalObject C t)) (T0 : τ (@TerminalObject (Op_cat C) t))
  (P : τ (@KernelAdjunctionStructure C S t T))
  [A B X D : τ (Functor K C)] (b : τ (@Transf K C B X)) (c : τ (@Transf K C X D))
  (h : τ (@NativeSnakeInput K C t T A B X D b c)) : τ (Functor K (Functor_cat WalkingArrow_cat C))
≔ @transf_arrow_diagram_func K C A (@kernel_adjunction_family_func K C S t T P (@transf_arrow_diagram_func K C X D c))
    (@one_cat_native_snake_alpha K C S C1 t T T0 P A B X D b c h);

// θ=π_α∘ℓ:E⇒Q(α), with the positive orientation fixed by the two original factors.
symbol one_cat_native_snake_covered_transf [K C : Cat] [S : τ (@PreadditiveCategory C)]
  (C1 : τ (IsNCat (cat_succ cat_zero) C)) [t : τ (Obj C)]
  (T : τ (@TerminalObject C t)) (T0 : τ (@TerminalObject (Op_cat C) t))
  (P : τ (@KernelAdjunctionStructure C S t T)) (Q : τ (@CokernelAdjunctionStructure C S t T0))
  [A B X D : τ (Functor K C)] (b : τ (@Transf K C B X)) (c : τ (@Transf K C X D))
  (h : τ (@NativeSnakeInput K C t T A B X D b c))
  : τ (@Transf K C (@one_cat_native_snake_cover_source K C S C1 t T T0 P Q A B X D b c h)
      (@cokernel_adjunction_family_func K C S t T0 Q (@one_cat_native_snake_alpha_diagram K C S C1 t T T0 P A B X D b c h)))
≔ @comp_fapp0 (Functor_cat K C) (@one_cat_native_snake_cover_source K C S C1 t T T0 P Q A B X D b c h)
    (@kernel_adjunction_family_func K C S t T P (@transf_arrow_diagram_func K C X D c))
    (@cokernel_adjunction_family_func K C S t T0 Q (@one_cat_native_snake_alpha_diagram K C S C1 t T T0 P A B X D b c h))
    (@cokernel_adjunction_family_projection_transf K C S t T0 Q (@one_cat_native_snake_alpha_diagram K C S C1 t T T0 P A B X D b c h))
    (@one_cat_native_snake_covered_lift K C S C1 t T T0 P Q A B X D b c h);
