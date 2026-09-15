/* The original native cover E=K(γ∘π_a)⇒K(γ).
   Its cover evidence is ΩAlong on Coim(ρ)⇒K(γ), not invertibility of ρ. */
require open emdash.emdash3_2_one_cat_native_snake_factors;
require open emdash.emdash3_2_one_cat_kernel_precomposition_covers;
require open emdash.emdash3_2_one_cat_quotient_cokernel_zero;

// The actual outgoing diagram of γ:Q(a)⇒D.
symbol one_cat_native_snake_gamma_diagram [K C : Cat] [S : τ (@PreadditiveCategory C)]
  (C1 : τ (IsNCat (cat_succ cat_zero) C)) [t : τ (Obj C)]
  (T : τ (@TerminalObject C t)) (T0 : τ (@TerminalObject (Op_cat C) t))
  (Q : τ (@CokernelAdjunctionStructure C S t T0))
  [A B X D : τ (Functor K C)] (b : τ (@Transf K C B X)) (c : τ (@Transf K C X D))
  (h : τ (@NativeSnakeInput K C t T A B X D b c)) : τ (Functor K (Functor_cat WalkingArrow_cat C))
≔ @transf_arrow_diagram_func K C
    (@cokernel_adjunction_family_func K C S t T0 Q (@native_snake_incoming_diagram K C t T A B X D b c h)) D
    (@one_cat_native_snake_gamma K C S C1 t T T0 Q A B X D b c h);

// π_a remains the projection of Q at the original incoming diagram.
symbol native_snake_quotient_transf [K C : Cat] [S : τ (@PreadditiveCategory C)]
  [t : τ (Obj C)] (T : τ (@TerminalObject C t)) (T0 : τ (@TerminalObject (Op_cat C) t))
  (Q : τ (@CokernelAdjunctionStructure C S t T0))
  [A B X D : τ (Functor K C)] (b : τ (@Transf K C B X)) (c : τ (@Transf K C X D))
  (h : τ (@NativeSnakeInput K C t T A B X D b c))
  : τ (@Transf K C B (@cokernel_adjunction_family_func K C S t T0 Q (@native_snake_incoming_diagram K C t T A B X D b c h)))
≔ @cokernel_adjunction_family_projection_transf K C S t T0 Q (@native_snake_incoming_diagram K C t T A B X D b c h);

// E=K(γ∘π_a); use the original whole kernel-of-precomposition owner.
symbol one_cat_native_snake_cover_source [K C : Cat] [S : τ (@PreadditiveCategory C)]
  (C1 : τ (IsNCat (cat_succ cat_zero) C)) [t : τ (Obj C)]
  (T : τ (@TerminalObject C t)) (T0 : τ (@TerminalObject (Op_cat C) t))
  (P : τ (@KernelAdjunctionStructure C S t T)) (Q : τ (@CokernelAdjunctionStructure C S t T0))
  [A B X D : τ (Functor K C)] (b : τ (@Transf K C B X)) (c : τ (@Transf K C X D))
  (h : τ (@NativeSnakeInput K C t T A B X D b c)) : τ (Functor K C)
≔ @kernel_precomposition_family_func K C S t T P B
    (@one_cat_native_snake_gamma_diagram K C S C1 t T T0 Q A B X D b c h)
    (@native_snake_quotient_transf K C S t T T0 Q A B X D b c h);

// The original first projection E⇒B.
symbol one_cat_native_snake_cover_first [K C : Cat] [S : τ (@PreadditiveCategory C)]
  (C1 : τ (IsNCat (cat_succ cat_zero) C)) [t : τ (Obj C)]
  (T : τ (@TerminalObject C t)) (T0 : τ (@TerminalObject (Op_cat C) t))
  (P : τ (@KernelAdjunctionStructure C S t T)) (Q : τ (@CokernelAdjunctionStructure C S t T0))
  [A B X D : τ (Functor K C)] (b : τ (@Transf K C B X)) (c : τ (@Transf K C X D))
  (h : τ (@NativeSnakeInput K C t T A B X D b c))
  : τ (@Transf K C (@one_cat_native_snake_cover_source K C S C1 t T T0 P Q A B X D b c h) B)
≔ @kernel_precomposition_first_transf K C S t T P B
    (@one_cat_native_snake_gamma_diagram K C S C1 t T T0 Q A B X D b c h)
    (@native_snake_quotient_transf K C S t T T0 Q A B X D b c h);

// ρ:E⇒K(γ) is the existing second comparison, without a chosen section.
symbol one_cat_native_snake_cover_transf [K C : Cat] [S : τ (@PreadditiveCategory C)]
  (C1 : τ (IsNCat (cat_succ cat_zero) C)) [t : τ (Obj C)]
  (T : τ (@TerminalObject C t)) (T0 : τ (@TerminalObject (Op_cat C) t))
  (P : τ (@KernelAdjunctionStructure C S t T)) (Q : τ (@CokernelAdjunctionStructure C S t T0))
  [A B X D : τ (Functor K C)] (b : τ (@Transf K C B X)) (c : τ (@Transf K C X D))
  (h : τ (@NativeSnakeInput K C t T A B X D b c))
  : τ (@Transf K C (@one_cat_native_snake_cover_source K C S C1 t T T0 P Q A B X D b c h)
      (@kernel_adjunction_family_func K C S t T P (@one_cat_native_snake_gamma_diagram K C S C1 t T T0 Q A B X D b c h)))
≔ @one_cat_kernel_precomposition_second_transf K C S C1 t T T0 P B
    (@one_cat_native_snake_gamma_diagram K C S C1 t T T0 Q A B X D b c h)
    (@native_snake_quotient_transf K C S t T T0 Q A B X D b c h);

// The whole square reconstructs π_a∘κ_E through the original κ_γ.
symbol one_cat_native_snake_cover_reconstruction [K C : Cat] [S : τ (@PreadditiveCategory C)]
  (C1 : τ (IsNCat (cat_succ cat_zero) C)) [t : τ (Obj C)]
  (T : τ (@TerminalObject C t)) (T0 : τ (@TerminalObject (Op_cat C) t))
  (P : τ (@KernelAdjunctionStructure C S t T)) (Q : τ (@CokernelAdjunctionStructure C S t T0))
  [A B X D : τ (Functor K C)] (b : τ (@Transf K C B X)) (c : τ (@Transf K C X D))
  (h : τ (@NativeSnakeInput K C t T A B X D b c))
≔ @one_cat_kernel_precomposition_square_path K C S C1 t T T0 P B
    (@one_cat_native_snake_gamma_diagram K C S C1 t T T0 Q A B X D b c h)
    (@native_snake_quotient_transf K C S t T T0 Q A B X D b c h);

// Alias of the existing categorical cover theorem, on this original ρ.
// Its needed cokernel-zero premise is derived from π_a's original Q unit.
symbol one_cat_native_snake_cover_omega [K C : Cat]
  (C1 : τ (IsNCat (cat_succ cat_zero) C))
  [Prod : τ (Functor (Product_cat C C) C)] [t : τ (Obj C)]
  (Add : τ (@AdditiveCategory C Prod t)) (T0 : τ (@TerminalObject (Op_cat C) t))
  (P : τ (@KernelAdjunctionStructure C (@additive_preadditive C Prod t Add) t (@additive_terminal_object C Prod t Add)))
  (Q : τ (@CokernelAdjunctionStructure C (@additive_preadditive C Prod t Add) t T0))
  (N : τ (@OneCatAdjunctionNormality C (@additive_preadditive C Prod t Add) C1 t (@additive_terminal_object C Prod t Add) T0 P Q))
  [A B X D : τ (Functor K C)] (b : τ (@Transf K C B X)) (c : τ (@Transf K C X D))
  (h : τ (@NativeSnakeInput K C t (@additive_terminal_object C Prod t Add) A B X D b c))
≔ @one_cat_kernel_precomposition_cover_omega K C C1 Prod t Add T0 P Q N B
    (@one_cat_native_snake_gamma_diagram K C (@additive_preadditive C Prod t Add) C1 t (@additive_terminal_object C Prod t Add) T0 Q A B X D b c h)
    (@native_snake_quotient_transf K C (@additive_preadditive C Prod t Add) t (@additive_terminal_object C Prod t Add) T0 Q A B X D b c h)
    (@one_cat_quotient_cokernel_zero K C (@additive_preadditive C Prod t Add) C1 t (@additive_terminal_object C Prod t Add) T0 Q
      (@native_snake_incoming_diagram K C t (@additive_terminal_object C Prod t Add) A B X D b c h));

// Whole cancellation through this original ρ, using the same coimage-cover proof.
symbol one_cat_native_snake_cover_reflect_path [K C : Cat]
  (C1 : τ (IsNCat (cat_succ cat_zero) C))
  [Prod : τ (Functor (Product_cat C C) C)] [t : τ (Obj C)]
  (Add : τ (@AdditiveCategory C Prod t)) (T0 : τ (@TerminalObject (Op_cat C) t))
  (P : τ (@KernelAdjunctionStructure C (@additive_preadditive C Prod t Add) t (@additive_terminal_object C Prod t Add)))
  (Q : τ (@CokernelAdjunctionStructure C (@additive_preadditive C Prod t Add) t T0))
  (N : τ (@OneCatAdjunctionNormality C (@additive_preadditive C Prod t Add) C1 t (@additive_terminal_object C Prod t Add) T0 P Q))
  [A B X D : τ (Functor K C)] (b : τ (@Transf K C B X)) (c : τ (@Transf K C X D))
  (h : τ (@NativeSnakeInput K C t (@additive_terminal_object C Prod t Add) A B X D b c))
  (Y : τ (Functor K C)) (u v : τ (@Transf K C (@kernel_adjunction_family_func K C (@additive_preadditive C Prod t Add) t (@additive_terminal_object C Prod t Add) P (@one_cat_native_snake_gamma_diagram K C (@additive_preadditive C Prod t Add) C1 t (@additive_terminal_object C Prod t Add) T0 Q A B X D b c h)) Y))
  (p : τ (@= (@Transf K C (@one_cat_native_snake_cover_source K C (@additive_preadditive C Prod t Add) C1 t (@additive_terminal_object C Prod t Add) T0 P Q A B X D b c h) Y)
    (@comp_fapp0 (Functor_cat K C) (@one_cat_native_snake_cover_source K C (@additive_preadditive C Prod t Add) C1 t (@additive_terminal_object C Prod t Add) T0 P Q A B X D b c h) (@kernel_adjunction_family_func K C (@additive_preadditive C Prod t Add) t (@additive_terminal_object C Prod t Add) P (@one_cat_native_snake_gamma_diagram K C (@additive_preadditive C Prod t Add) C1 t (@additive_terminal_object C Prod t Add) T0 Q A B X D b c h)) Y u (@one_cat_native_snake_cover_transf K C (@additive_preadditive C Prod t Add) C1 t (@additive_terminal_object C Prod t Add) T0 P Q A B X D b c h))
    (@comp_fapp0 (Functor_cat K C) (@one_cat_native_snake_cover_source K C (@additive_preadditive C Prod t Add) C1 t (@additive_terminal_object C Prod t Add) T0 P Q A B X D b c h) (@kernel_adjunction_family_func K C (@additive_preadditive C Prod t Add) t (@additive_terminal_object C Prod t Add) P (@one_cat_native_snake_gamma_diagram K C (@additive_preadditive C Prod t Add) C1 t (@additive_terminal_object C Prod t Add) T0 Q A B X D b c h)) Y v (@one_cat_native_snake_cover_transf K C (@additive_preadditive C Prod t Add) C1 t (@additive_terminal_object C Prod t Add) T0 P Q A B X D b c h))))
  : τ (@= (@Transf K C (@kernel_adjunction_family_func K C (@additive_preadditive C Prod t Add) t (@additive_terminal_object C Prod t Add) P (@one_cat_native_snake_gamma_diagram K C (@additive_preadditive C Prod t Add) C1 t (@additive_terminal_object C Prod t Add) T0 Q A B X D b c h)) Y) u v)
≔ @one_cat_coimage_cover_reflect_path K C (@additive_preadditive C Prod t Add) C1 t (@additive_terminal_object C Prod t Add) T0 P Q
    (@transf_arrow_diagram_func K C (@one_cat_native_snake_cover_source K C (@additive_preadditive C Prod t Add) C1 t (@additive_terminal_object C Prod t Add) T0 P Q A B X D b c h) (@kernel_adjunction_family_func K C (@additive_preadditive C Prod t Add) t (@additive_terminal_object C Prod t Add) P (@one_cat_native_snake_gamma_diagram K C (@additive_preadditive C Prod t Add) C1 t (@additive_terminal_object C Prod t Add) T0 Q A B X D b c h)) (@one_cat_native_snake_cover_transf K C (@additive_preadditive C Prod t Add) C1 t (@additive_terminal_object C Prod t Add) T0 P Q A B X D b c h))
    (@one_cat_native_snake_cover_omega K C C1 Prod t Add T0 P Q N A B X D b c h) Y u v p;
