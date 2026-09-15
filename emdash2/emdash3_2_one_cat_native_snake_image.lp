/* Original image factorization and whole cancellation for the general snake. */
require open emdash.emdash3_2_one_cat_image_family_covers;
require open emdash.emdash3_2_one_cat_native_snake_covered_map;

// The image uses the ORIGINAL Q-arrow family before applying the original K.
symbol one_cat_native_snake_image_func [K C : Cat] [S : τ (@PreadditiveCategory C)]
  (C1 : τ (IsNCat (cat_succ cat_zero) C)) [t : τ (Obj C)]
  (T : τ (@TerminalObject C t)) (T0 : τ (@TerminalObject (Op_cat C) t))
  (P : τ (@KernelAdjunctionStructure C S t T)) (Q : τ (@CokernelAdjunctionStructure C S t T0))
  [A B X D : τ (Functor K C)] (b : τ (@Transf K C B X)) (c : τ (@Transf K C X D))
  (h : τ (@NativeSnakeInput K C t T A B X D b c))
  : τ (Functor K C)
≔ (@kernel_adjunction_family_func K C S t T P (@comp_cat_fapp0 K (Functor_cat WalkingArrow_cat C) (Functor_cat
  WalkingArrow_cat C) (@cokernel_adjunction_arrow_func C S t T0 Q) (@native_snake_incoming_diagram K C t T A B X
  D b c h)));

// The same original image kernel inclusion.
symbol one_cat_native_snake_image_inclusion [K C : Cat] [S : τ (@PreadditiveCategory C)]
  (C1 : τ (IsNCat (cat_succ cat_zero) C)) [t : τ (Obj C)]
  (T : τ (@TerminalObject C t)) (T0 : τ (@TerminalObject (Op_cat C) t))
  (P : τ (@KernelAdjunctionStructure C S t T)) (Q : τ (@CokernelAdjunctionStructure C S t T0))
  [A B X D : τ (Functor K C)] (b : τ (@Transf K C B X)) (c : τ (@Transf K C X D))
  (h : τ (@NativeSnakeInput K C t T A B X D b c))
  : τ (@Transf K C (@one_cat_native_snake_image_func K C S C1 t T T0 P Q A B X D b c h) B)
≔ (@kernel_adjunction_family_inclusion_transf K C S t T P (@comp_cat_fapp0 K (Functor_cat WalkingArrow_cat C)
  (Functor_cat WalkingArrow_cat C) (@cokernel_adjunction_arrow_func C S t T0 Q) (@native_snake_incoming_diagram
  K C t T A B X D b c h)));

// The original coimage quotient followed by the fixed comparison.
symbol one_cat_native_snake_source_image [K C : Cat] [S : τ (@PreadditiveCategory C)]
  (C1 : τ (IsNCat (cat_succ cat_zero) C)) [t : τ (Obj C)]
  (T : τ (@TerminalObject C t)) (T0 : τ (@TerminalObject (Op_cat C) t))
  (P : τ (@KernelAdjunctionStructure C S t T)) (Q : τ (@CokernelAdjunctionStructure C S t T0))
  [A B X D : τ (Functor K C)] (b : τ (@Transf K C B X)) (c : τ (@Transf K C X D))
  (h : τ (@NativeSnakeInput K C t T A B X D b c))
  : τ (@Transf K C A (@one_cat_native_snake_image_func K C S C1 t T T0 P Q A B X D b c h))
≔ (@one_cat_image_family_source_transf K C S C1 t T T0 P Q (@native_snake_incoming_diagram K C t T A B X D b c
  h));

// The whole image factorization recovers the original a.
symbol one_cat_native_snake_image_factor_path [K C : Cat] [S : τ (@PreadditiveCategory C)]
  (C1 : τ (IsNCat (cat_succ cat_zero) C)) [t : τ (Obj C)]
  (T : τ (@TerminalObject C t)) (T0 : τ (@TerminalObject (Op_cat C) t))
  (P : τ (@KernelAdjunctionStructure C S t T)) (Q : τ (@CokernelAdjunctionStructure C S t T0))
  [A B X D : τ (Functor K C)] (b : τ (@Transf K C B X)) (c : τ (@Transf K C X D))
  (h : τ (@NativeSnakeInput K C t T A B X D b c))
  : τ (@= (@Transf K C A B) (@comp_fapp0 (Functor_cat K C) A (@one_cat_native_snake_image_func K C S C1 t T T0 P
    Q A B X D b c h) B (@one_cat_native_snake_image_inclusion K C S C1 t T T0 P Q A B X D b c h)
    (@one_cat_native_snake_source_image K C S C1 t T T0 P Q A B X D b c h)) (@native_snake_incoming K C t T A B
    X D b c h))
≔ (@one_cat_image_family_source_factor_path K C S C1 t T T0 P Q (@native_snake_incoming_diagram K C t T A B X D
  b c h));

// γπ_a=cb and π_aκ_Im=0 make bκ_Im a native K(c)-mate input.
symbol one_cat_native_snake_image_zero [K C : Cat] [S : τ (@PreadditiveCategory C)]
  (C1 : τ (IsNCat (cat_succ cat_zero) C)) [t : τ (Obj C)]
  (T : τ (@TerminalObject C t)) (T0 : τ (@TerminalObject (Op_cat C) t))
  (P : τ (@KernelAdjunctionStructure C S t T)) (Q : τ (@CokernelAdjunctionStructure C S t T0))
  [A B X D : τ (Functor K C)] (b : τ (@Transf K C B X)) (c : τ (@Transf K C X D))
  (h : τ (@NativeSnakeInput K C t T A B X D b c))
  : τ (@= (@Transf K C (@one_cat_native_snake_image_func K C S C1 t T T0 P Q A B X D b c h) D) (@comp_fapp0
    (Functor_cat K C) (@one_cat_native_snake_image_func K C S C1 t T T0 P Q A B X D b c h) X D c (@comp_fapp0
    (Functor_cat K C) (@one_cat_native_snake_image_func K C S C1 t T T0 P Q A B X D b c h) B X b
    (@one_cat_native_snake_image_inclusion K C S C1 t T T0 P Q A B X D b c h))) (@zero_arrow_family_zero_transf
    K C t T T0 (@one_cat_native_snake_image_func K C S C1 t T T0 P Q A B X D b c h) D))
≔ (@eq_trans _ _ _ _ (@comp_assoc (Functor_cat K C) (@one_cat_native_snake_image_func K C S C1 t T T0 P Q A B X
  D b c h) B X D c b (@one_cat_native_snake_image_inclusion K C S C1 t T T0 P Q A B X D b c h)) (@eq_trans _ _ _
  _ (@eq_ap (@Transf K C B D) (@Transf K C (@one_cat_native_snake_image_func K C S C1 t T T0 P Q A B X D b c h)
  D) (λ v : τ (@Transf K C B D), (@comp_fapp0 (Functor_cat K C) (@one_cat_native_snake_image_func K C S C1 t T
  T0 P Q A B X D b c h) B D v (@one_cat_native_snake_image_inclusion K C S C1 t T T0 P Q A B X D b c h))) _ _
  (@eq_sym _ _ _ (@one_cat_native_snake_gamma_reconstruction K C S C1 t T T0 Q A B X D b c h))) (@eq_trans _ _ _
  _ (@eq_sym _ _ _ (@comp_assoc (Functor_cat K C) (@one_cat_native_snake_image_func K C S C1 t T T0 P Q A B X D
  b c h) B (@cokernel_adjunction_family_func K C S t T0 Q (@native_snake_incoming_diagram K C t T A B X D b c
  h)) D (@one_cat_native_snake_gamma K C S C1 t T T0 Q A B X D b c h) (@native_snake_quotient_transf K C S t T
  T0 Q A B X D b c h) (@one_cat_native_snake_image_inclusion K C S C1 t T T0 P Q A B X D b c h))) (@eq_trans _ _
  _ _ (@eq_ap (@Transf K C (@one_cat_native_snake_image_func K C S C1 t T T0 P Q A B X D b c h)
  (@cokernel_adjunction_family_func K C S t T0 Q (@native_snake_incoming_diagram K C t T A B X D b c h)))
  (@Transf K C (@one_cat_native_snake_image_func K C S C1 t T T0 P Q A B X D b c h) D) (λ v : τ (@Transf K C
  (@one_cat_native_snake_image_func K C S C1 t T T0 P Q A B X D b c h) (@cokernel_adjunction_family_func K C S t
  T0 Q (@native_snake_incoming_diagram K C t T A B X D b c h))), (@comp_fapp0 (Functor_cat K C)
  (@one_cat_native_snake_image_func K C S C1 t T T0 P Q A B X D b c h) (@cokernel_adjunction_family_func K C S t
  T0 Q (@native_snake_incoming_diagram K C t T A B X D b c h)) D (@one_cat_native_snake_gamma K C S C1 t T T0 Q
  A B X D b c h) v)) _ _ (@one_cat_kernel_family_annihilation_path K C S C1 t T T0 P (@comp_cat_fapp0 K
  (Functor_cat WalkingArrow_cat C) (Functor_cat WalkingArrow_cat C) (@cokernel_adjunction_arrow_func C S t T0 Q)
  (@native_snake_incoming_diagram K C t T A B X D b c h)))) (@one_cat_zero_family_postcompose_path K C C1 t T T0
  (@one_cat_native_snake_image_func K C S C1 t T T0 P Q A B X D b c h) (@cokernel_adjunction_family_func K C S t
  T0 Q (@native_snake_incoming_diagram K C t T A B X D b c h)) D (@one_cat_native_snake_gamma K C S C1 t T T0 Q
  A B X D b c h))))));

// Lift bκ_Im through the original whole K(c).
symbol one_cat_native_snake_image_lift [K C : Cat] [S : τ (@PreadditiveCategory C)]
  (C1 : τ (IsNCat (cat_succ cat_zero) C)) [t : τ (Obj C)]
  (T : τ (@TerminalObject C t)) (T0 : τ (@TerminalObject (Op_cat C) t))
  (P : τ (@KernelAdjunctionStructure C S t T)) (Q : τ (@CokernelAdjunctionStructure C S t T0))
  [A B X D : τ (Functor K C)] (b : τ (@Transf K C B X)) (c : τ (@Transf K C X D))
  (h : τ (@NativeSnakeInput K C t T A B X D b c))
  : τ (@Transf K C (@one_cat_native_snake_image_func K C S C1 t T T0 P Q A B X D b c h)
    (@kernel_adjunction_family_func K C S t T P (@transf_arrow_diagram_func K C X D c)))
≔ (@one_cat_kernel_family_lift K C S C1 t T T0 P (@one_cat_native_snake_image_func K C S C1 t T T0 P Q A B X D b
  c h) (@transf_arrow_diagram_func K C X D c) (@comp_fapp0 (Functor_cat K C) (@one_cat_native_snake_image_func K
  C S C1 t T T0 P Q A B X D b c h) B X b (@one_cat_native_snake_image_inclusion K C S C1 t T T0 P Q A B X D b c
  h)) (@one_cat_native_snake_image_zero K C S C1 t T T0 P Q A B X D b c h));

// The whole lift reconstructs bκ_Im.
symbol one_cat_native_snake_image_lift_reconstruction [K C : Cat] [S : τ (@PreadditiveCategory C)]
  (C1 : τ (IsNCat (cat_succ cat_zero) C)) [t : τ (Obj C)]
  (T : τ (@TerminalObject C t)) (T0 : τ (@TerminalObject (Op_cat C) t))
  (P : τ (@KernelAdjunctionStructure C S t T)) (Q : τ (@CokernelAdjunctionStructure C S t T0))
  [A B X D : τ (Functor K C)] (b : τ (@Transf K C B X)) (c : τ (@Transf K C X D))
  (h : τ (@NativeSnakeInput K C t T A B X D b c))
  : τ (@= (@Transf K C (@one_cat_native_snake_image_func K C S C1 t T T0 P Q A B X D b c h) X) (@comp_fapp0
    (Functor_cat K C) (@one_cat_native_snake_image_func K C S C1 t T T0 P Q A B X D b c h)
    (@kernel_adjunction_family_func K C S t T P (@transf_arrow_diagram_func K C X D c)) X
    (@kernel_adjunction_family_inclusion_transf K C S t T P (@transf_arrow_diagram_func K C X D c))
    (@one_cat_native_snake_image_lift K C S C1 t T T0 P Q A B X D b c h)) (@comp_fapp0 (Functor_cat K C)
    (@one_cat_native_snake_image_func K C S C1 t T T0 P Q A B X D b c h) B X b
    (@one_cat_native_snake_image_inclusion K C S C1 t T T0 P Q A B X D b c h)))
≔ (@one_cat_kernel_family_lift_ambient_reconstruction K C S C1 t T T0 P (@one_cat_native_snake_image_func K C S
  C1 t T T0 P Q A B X D b c h) (@transf_arrow_diagram_func K C X D c) (@comp_fapp0 (Functor_cat K C)
  (@one_cat_native_snake_image_func K C S C1 t T T0 P Q A B X D b c h) B X b
  (@one_cat_native_snake_image_inclusion K C S C1 t T T0 P Q A B X D b c h)) (@one_cat_native_snake_image_zero K
  C S C1 t T T0 P Q A B X D b c h));

// Native kernel cancellation identifies v∘s_a with the original α.
symbol one_cat_native_snake_image_lift_source_path [K C : Cat] [S : τ (@PreadditiveCategory C)]
  (C1 : τ (IsNCat (cat_succ cat_zero) C)) [t : τ (Obj C)]
  (T : τ (@TerminalObject C t)) (T0 : τ (@TerminalObject (Op_cat C) t))
  (P : τ (@KernelAdjunctionStructure C S t T)) (Q : τ (@CokernelAdjunctionStructure C S t T0))
  [A B X D : τ (Functor K C)] (b : τ (@Transf K C B X)) (c : τ (@Transf K C X D))
  (h : τ (@NativeSnakeInput K C t T A B X D b c))
  : τ (@= (@Transf K C A (@kernel_adjunction_family_func K C S t T P (@transf_arrow_diagram_func K C X D c)))
    (@comp_fapp0 (Functor_cat K C) A (@one_cat_native_snake_image_func K C S C1 t T T0 P Q A B X D b c h)
    (@kernel_adjunction_family_func K C S t T P (@transf_arrow_diagram_func K C X D c))
    (@one_cat_native_snake_image_lift K C S C1 t T T0 P Q A B X D b c h) (@one_cat_native_snake_source_image K C
    S C1 t T T0 P Q A B X D b c h)) (@one_cat_native_snake_alpha K C S C1 t T T0 P A B X D b c h))
≔ (@one_cat_kernel_family_inclusion_reflect_path K C S C1 t T T0 P A (@transf_arrow_diagram_func K C X D c)
  (@comp_fapp0 (Functor_cat K C) A (@one_cat_native_snake_image_func K C S C1 t T T0 P Q A B X D b c h)
  (@kernel_adjunction_family_func K C S t T P (@transf_arrow_diagram_func K C X D c))
  (@one_cat_native_snake_image_lift K C S C1 t T T0 P Q A B X D b c h) (@one_cat_native_snake_source_image K C S
  C1 t T T0 P Q A B X D b c h)) (@one_cat_native_snake_alpha K C S C1 t T T0 P A B X D b c h) (@eq_trans _ _ _ _
  (@comp_assoc (Functor_cat K C) A (@one_cat_native_snake_image_func K C S C1 t T T0 P Q A B X D b c h)
  (@kernel_adjunction_family_func K C S t T P (@transf_arrow_diagram_func K C X D c)) X
  (@kernel_adjunction_family_inclusion_transf K C S t T P (@transf_arrow_diagram_func K C X D c))
  (@one_cat_native_snake_image_lift K C S C1 t T T0 P Q A B X D b c h) (@one_cat_native_snake_source_image K C S
  C1 t T T0 P Q A B X D b c h)) (@eq_trans _ _ _ _ (@eq_ap (@Transf K C (@one_cat_native_snake_image_func K C S
  C1 t T T0 P Q A B X D b c h) X) (@Transf K C A X) (λ v : τ (@Transf K C (@one_cat_native_snake_image_func K C
  S C1 t T T0 P Q A B X D b c h) X), (@comp_fapp0 (Functor_cat K C) A (@one_cat_native_snake_image_func K C S C1
  t T T0 P Q A B X D b c h) X v (@one_cat_native_snake_source_image K C S C1 t T T0 P Q A B X D b c h))) _ _
  (@one_cat_native_snake_image_lift_reconstruction K C S C1 t T T0 P Q A B X D b c h)) (@eq_trans _ _ _ _
  (@eq_sym _ _ _ (@comp_assoc (Functor_cat K C) A (@one_cat_native_snake_image_func K C S C1 t T T0 P Q A B X D
  b c h) B X b (@one_cat_native_snake_image_inclusion K C S C1 t T T0 P Q A B X D b c h)
  (@one_cat_native_snake_source_image K C S C1 t T T0 P Q A B X D b c h))) (@eq_trans _ _ _ _ (@eq_ap (@Transf K
  C A B) (@Transf K C A X) (λ v : τ (@Transf K C A B), (@comp_fapp0 (Functor_cat K C) A B X b v)) _ _
  (@one_cat_native_snake_image_factor_path K C S C1 t T T0 P Q A B X D b c h)) (@eq_sym _ _ _
  (@one_cat_native_snake_alpha_reconstruction K C S C1 t T T0 P A B X D b c h)))))));

// Whole image-source cancellation derives π_α∘v=0; no annihilation premise is added.
symbol one_cat_native_snake_image_quotient_zero [K C : Cat] [S : τ (@PreadditiveCategory C)]
  (C1 : τ (IsNCat (cat_succ cat_zero) C)) [t : τ (Obj C)]
  (T : τ (@TerminalObject C t)) (T0 : τ (@TerminalObject (Op_cat C) t))
  (P : τ (@KernelAdjunctionStructure C S t T)) (Q : τ (@CokernelAdjunctionStructure C S t T0))
  (N : τ (@OneCatAdjunctionNormality C S C1 t T T0 P Q))
  [A B X D : τ (Functor K C)] (b : τ (@Transf K C B X)) (c : τ (@Transf K C X D))
  (h : τ (@NativeSnakeInput K C t T A B X D b c))
  : τ (@= (@Transf K C (@one_cat_native_snake_image_func K C S C1 t T T0 P Q A B X D b c h)
    (@cokernel_adjunction_family_func K C S t T0 Q (@one_cat_native_snake_alpha_diagram K C S C1 t T T0 P A B X
    D b c h))) (@comp_fapp0 (Functor_cat K C) (@one_cat_native_snake_image_func K C S C1 t T T0 P Q A B X D b c
    h) (@kernel_adjunction_family_func K C S t T P (@transf_arrow_diagram_func K C X D c))
    (@cokernel_adjunction_family_func K C S t T0 Q (@one_cat_native_snake_alpha_diagram K C S C1 t T T0 P A B X
    D b c h)) (@cokernel_adjunction_family_projection_transf K C S t T0 Q (@one_cat_native_snake_alpha_diagram K
    C S C1 t T T0 P A B X D b c h)) (@one_cat_native_snake_image_lift K C S C1 t T T0 P Q A B X D b c h))
    (@zero_arrow_family_zero_transf K C t T T0 (@one_cat_native_snake_image_func K C S C1 t T T0 P Q A B X D b c
    h) (@cokernel_adjunction_family_func K C S t T0 Q (@one_cat_native_snake_alpha_diagram K C S C1 t T T0 P A B
    X D b c h))))
≔ (@one_cat_image_family_source_reflect_path K C S C1 t T T0 P Q N (@native_snake_incoming_diagram K C t T A B X
  D b c h) (@cokernel_adjunction_family_func K C S t T0 Q (@one_cat_native_snake_alpha_diagram K C S C1 t T T0 P
  A B X D b c h)) (@comp_fapp0 (Functor_cat K C) (@one_cat_native_snake_image_func K C S C1 t T T0 P Q A B X D b
  c h) (@kernel_adjunction_family_func K C S t T P (@transf_arrow_diagram_func K C X D c))
  (@cokernel_adjunction_family_func K C S t T0 Q (@one_cat_native_snake_alpha_diagram K C S C1 t T T0 P A B X D
  b c h)) (@cokernel_adjunction_family_projection_transf K C S t T0 Q (@one_cat_native_snake_alpha_diagram K C S
  C1 t T T0 P A B X D b c h)) (@one_cat_native_snake_image_lift K C S C1 t T T0 P Q A B X D b c h))
  (@zero_arrow_family_zero_transf K C t T T0 (@one_cat_native_snake_image_func K C S C1 t T T0 P Q A B X D b c
  h) (@cokernel_adjunction_family_func K C S t T0 Q (@one_cat_native_snake_alpha_diagram K C S C1 t T T0 P A B X
  D b c h))) (@eq_trans _ _ _ _ (@eq_sym _ _ _ (@comp_assoc (Functor_cat K C) A
  (@one_cat_native_snake_image_func K C S C1 t T T0 P Q A B X D b c h) (@kernel_adjunction_family_func K C S t T
  P (@transf_arrow_diagram_func K C X D c)) (@cokernel_adjunction_family_func K C S t T0 Q
  (@one_cat_native_snake_alpha_diagram K C S C1 t T T0 P A B X D b c h))
  (@cokernel_adjunction_family_projection_transf K C S t T0 Q (@one_cat_native_snake_alpha_diagram K C S C1 t T
  T0 P A B X D b c h)) (@one_cat_native_snake_image_lift K C S C1 t T T0 P Q A B X D b c h)
  (@one_cat_native_snake_source_image K C S C1 t T T0 P Q A B X D b c h))) (@eq_trans _ _ _ _ (@eq_ap (@Transf K
  C A (@kernel_adjunction_family_func K C S t T P (@transf_arrow_diagram_func K C X D c))) (@Transf K C A
  (@cokernel_adjunction_family_func K C S t T0 Q (@one_cat_native_snake_alpha_diagram K C S C1 t T T0 P A B X D
  b c h))) (λ v : τ (@Transf K C A (@kernel_adjunction_family_func K C S t T P (@transf_arrow_diagram_func K C X
  D c))), (@comp_fapp0 (Functor_cat K C) A (@kernel_adjunction_family_func K C S t T P
  (@transf_arrow_diagram_func K C X D c)) (@cokernel_adjunction_family_func K C S t T0 Q
  (@one_cat_native_snake_alpha_diagram K C S C1 t T T0 P A B X D b c h))
  (@cokernel_adjunction_family_projection_transf K C S t T0 Q (@one_cat_native_snake_alpha_diagram K C S C1 t T
  T0 P A B X D b c h)) v)) _ _ (@one_cat_native_snake_image_lift_source_path K C S C1 t T T0 P Q A B X D b c h))
  (@eq_trans _ _ _ _ (@one_cat_cokernel_family_annihilation_path K C S C1 t T T0 Q
  (@one_cat_native_snake_alpha_diagram K C S C1 t T T0 P A B X D b c h)) (@eq_sym _ _ _
  (@one_cat_zero_family_precompose_path K C C1 t T T0 A (@one_cat_native_snake_image_func K C S C1 t T T0 P Q A
  B X D b c h) (@cokernel_adjunction_family_func K C S t T0 Q (@one_cat_native_snake_alpha_diagram K C S C1 t T
  T0 P A B X D b c h)) (@one_cat_native_snake_source_image K C S C1 t T T0 P Q A B X D b c h)))))));
