/* Four surrounding native snake maps, using the two original reconstruction squares. */
require open emdash.emdash3_2_one_cat_native_snake_covered_map;
require open emdash.emdash3_2_one_cat_arrow_family_maps;
require open emdash.emdash3_2_one_cat_kernel_cokernel_family_maps;

// The native whole α→b square is derived from κ_c∘α=b∘a.
symbol one_cat_native_snake_first_diagram_map [K C : Cat] [S : τ (@PreadditiveCategory C)]
  (C1 : τ (IsNCat (cat_succ cat_zero) C)) [t : τ (Obj C)]
  (T : τ (@TerminalObject C t)) (T0 : τ (@TerminalObject (Op_cat C) t))
  (P : τ (@KernelAdjunctionStructure C S t T)) (Q : τ (@CokernelAdjunctionStructure C S t T0))
  [A B X D : τ (Functor K C)] (b : τ (@Transf K C B X)) (c : τ (@Transf K C X D))
  (h : τ (@NativeSnakeInput K C t T A B X D b c))
  : τ (@Transf K (Functor_cat WalkingArrow_cat C) (@one_cat_native_snake_alpha_diagram K C S C1 t T T0 P A B X D
    b c h) (@transf_arrow_diagram_func K C B X b))
≔ (@one_cat_square_family_transf K C C1 A B (@kernel_adjunction_family_func K C S t T P
  (@transf_arrow_diagram_func K C X D c)) X (@one_cat_native_snake_alpha K C S C1 t T T0 P A B X D b c h) b
  (@native_snake_incoming K C t T A B X D b c h) (@kernel_adjunction_family_inclusion_transf K C S t T P
  (@transf_arrow_diagram_func K C X D c)) (@one_cat_native_snake_alpha_reconstruction K C S C1 t T T0 P A B X D
  b c h));

// The native whole b→γ square is derived from γ∘π_a=c∘b.
symbol one_cat_native_snake_second_diagram_map [K C : Cat] [S : τ (@PreadditiveCategory C)]
  (C1 : τ (IsNCat (cat_succ cat_zero) C)) [t : τ (Obj C)]
  (T : τ (@TerminalObject C t)) (T0 : τ (@TerminalObject (Op_cat C) t))
  (P : τ (@KernelAdjunctionStructure C S t T)) (Q : τ (@CokernelAdjunctionStructure C S t T0))
  [A B X D : τ (Functor K C)] (b : τ (@Transf K C B X)) (c : τ (@Transf K C X D))
  (h : τ (@NativeSnakeInput K C t T A B X D b c))
  : τ (@Transf K (Functor_cat WalkingArrow_cat C) (@transf_arrow_diagram_func K C B X b)
    (@one_cat_native_snake_gamma_diagram K C S C1 t T T0 Q A B X D b c h))
≔ (@one_cat_square_family_transf K C C1 B (@cokernel_adjunction_family_func K C S t T0 Q
  (@native_snake_incoming_diagram K C t T A B X D b c h)) X D b (@one_cat_native_snake_gamma K C S C1 t T T0 Q A
  B X D b c h) (@cokernel_adjunction_family_projection_transf K C S t T0 Q (@native_snake_incoming_diagram K C t
  T A B X D b c h)) c (@eq_sym _ _ _ (@one_cat_native_snake_gamma_reconstruction K C S C1 t T T0 Q A B X D b c
  h)));

// The original whole kernel functor acts on the same first diagram map.
symbol one_cat_native_snake_kernel_first [K C : Cat] [S : τ (@PreadditiveCategory C)]
  (C1 : τ (IsNCat (cat_succ cat_zero) C)) [t : τ (Obj C)]
  (T : τ (@TerminalObject C t)) (T0 : τ (@TerminalObject (Op_cat C) t))
  (P : τ (@KernelAdjunctionStructure C S t T)) (Q : τ (@CokernelAdjunctionStructure C S t T0))
  [A B X D : τ (Functor K C)] (b : τ (@Transf K C B X)) (c : τ (@Transf K C X D))
  (h : τ (@NativeSnakeInput K C t T A B X D b c))
  : τ (@Transf K C (@kernel_adjunction_family_func K C S t T P (@one_cat_native_snake_alpha_diagram K C S C1 t T
    T0 P A B X D b c h)) (@kernel_adjunction_family_func K C S t T P (@transf_arrow_diagram_func K C B X b)))
≔ (@kernel_adjunction_family_map_transf K C S C1 t T T0 P Q (@one_cat_native_snake_alpha_diagram K C S C1 t T T0
  P A B X D b c h) (@transf_arrow_diagram_func K C B X b) (@one_cat_native_snake_first_diagram_map K C S C1 t T
  T0 P Q A B X D b c h));

// The original whole cokernel functor acts on the same first diagram map.
symbol one_cat_native_snake_cokernel_first [K C : Cat] [S : τ (@PreadditiveCategory C)]
  (C1 : τ (IsNCat (cat_succ cat_zero) C)) [t : τ (Obj C)]
  (T : τ (@TerminalObject C t)) (T0 : τ (@TerminalObject (Op_cat C) t))
  (P : τ (@KernelAdjunctionStructure C S t T)) (Q : τ (@CokernelAdjunctionStructure C S t T0))
  [A B X D : τ (Functor K C)] (b : τ (@Transf K C B X)) (c : τ (@Transf K C X D))
  (h : τ (@NativeSnakeInput K C t T A B X D b c))
  : τ (@Transf K C (@cokernel_adjunction_family_func K C S t T0 Q (@one_cat_native_snake_alpha_diagram K C S C1
    t T T0 P A B X D b c h)) (@cokernel_adjunction_family_func K C S t T0 Q (@transf_arrow_diagram_func K C B X
    b)))
≔ (@cokernel_adjunction_family_map_transf K C S C1 t T T0 P Q (@one_cat_native_snake_alpha_diagram K C S C1 t T
  T0 P A B X D b c h) (@transf_arrow_diagram_func K C B X b) (@one_cat_native_snake_first_diagram_map K C S C1 t
  T T0 P Q A B X D b c h));

// The original whole kernel functor acts on the same second diagram map.
symbol one_cat_native_snake_kernel_second [K C : Cat] [S : τ (@PreadditiveCategory C)]
  (C1 : τ (IsNCat (cat_succ cat_zero) C)) [t : τ (Obj C)]
  (T : τ (@TerminalObject C t)) (T0 : τ (@TerminalObject (Op_cat C) t))
  (P : τ (@KernelAdjunctionStructure C S t T)) (Q : τ (@CokernelAdjunctionStructure C S t T0))
  [A B X D : τ (Functor K C)] (b : τ (@Transf K C B X)) (c : τ (@Transf K C X D))
  (h : τ (@NativeSnakeInput K C t T A B X D b c))
  : τ (@Transf K C (@kernel_adjunction_family_func K C S t T P (@transf_arrow_diagram_func K C B X b))
    (@kernel_adjunction_family_func K C S t T P (@one_cat_native_snake_gamma_diagram K C S C1 t T T0 Q A B X D b
    c h)))
≔ (@kernel_adjunction_family_map_transf K C S C1 t T T0 P Q (@transf_arrow_diagram_func K C B X b)
  (@one_cat_native_snake_gamma_diagram K C S C1 t T T0 Q A B X D b c h)
  (@one_cat_native_snake_second_diagram_map K C S C1 t T T0 P Q A B X D b c h));

// The original whole cokernel functor acts on the same second diagram map.
symbol one_cat_native_snake_cokernel_second [K C : Cat] [S : τ (@PreadditiveCategory C)]
  (C1 : τ (IsNCat (cat_succ cat_zero) C)) [t : τ (Obj C)]
  (T : τ (@TerminalObject C t)) (T0 : τ (@TerminalObject (Op_cat C) t))
  (P : τ (@KernelAdjunctionStructure C S t T)) (Q : τ (@CokernelAdjunctionStructure C S t T0))
  [A B X D : τ (Functor K C)] (b : τ (@Transf K C B X)) (c : τ (@Transf K C X D))
  (h : τ (@NativeSnakeInput K C t T A B X D b c))
  : τ (@Transf K C (@cokernel_adjunction_family_func K C S t T0 Q (@transf_arrow_diagram_func K C B X b))
    (@cokernel_adjunction_family_func K C S t T0 Q (@one_cat_native_snake_gamma_diagram K C S C1 t T T0 Q A B X
    D b c h)))
≔ (@cokernel_adjunction_family_map_transf K C S C1 t T T0 P Q (@transf_arrow_diagram_func K C B X b)
  (@one_cat_native_snake_gamma_diagram K C S C1 t T T0 Q A B X D b c h)
  (@one_cat_native_snake_second_diagram_map K C S C1 t T T0 P Q A B X D b c h));

// Kernel action reconstructs the original source map of the first square.
symbol one_cat_native_snake_kernel_first_reconstruction [K C : Cat] [S : τ (@PreadditiveCategory C)]
  (C1 : τ (IsNCat (cat_succ cat_zero) C)) [t : τ (Obj C)]
  (T : τ (@TerminalObject C t)) (T0 : τ (@TerminalObject (Op_cat C) t))
  (P : τ (@KernelAdjunctionStructure C S t T)) (Q : τ (@CokernelAdjunctionStructure C S t T0))
  [A B X D : τ (Functor K C)] (b : τ (@Transf K C B X)) (c : τ (@Transf K C X D))
  (h : τ (@NativeSnakeInput K C t T A B X D b c))
  : τ (@= (@Transf K C (@kernel_adjunction_family_func K C S t T P (@one_cat_native_snake_alpha_diagram K C S C1
    t T T0 P A B X D b c h)) B) (@comp_fapp0 (Functor_cat K C) (@kernel_adjunction_family_func K C S t T P
    (@one_cat_native_snake_alpha_diagram K C S C1 t T T0 P A B X D b c h)) (@kernel_adjunction_family_func K C S
    t T P (@transf_arrow_diagram_func K C B X b)) B (@kernel_adjunction_family_inclusion_transf K C S t T P
    (@transf_arrow_diagram_func K C B X b)) (@one_cat_native_snake_kernel_first K C S C1 t T T0 P Q A B X D b c
    h)) (@comp_fapp0 (Functor_cat K C) (@kernel_adjunction_family_func K C S t T P
    (@one_cat_native_snake_alpha_diagram K C S C1 t T T0 P A B X D b c h)) A B (@native_snake_incoming K C t T A
    B X D b c h) (@kernel_adjunction_family_inclusion_transf K C S t T P (@one_cat_native_snake_alpha_diagram K
    C S C1 t T T0 P A B X D b c h))))
≔ (@eq_trans _ _ _ _ (@one_cat_kernel_family_map_inclusion_path K C S C1 t T T0 P Q
  (@one_cat_native_snake_alpha_diagram K C S C1 t T T0 P A B X D b c h) (@transf_arrow_diagram_func K C B X b)
  (@one_cat_native_snake_first_diagram_map K C S C1 t T T0 P Q A B X D b c h)) (@eq_ap (@Transf K C A B)
  (@Transf K C (@kernel_adjunction_family_func K C S t T P (@one_cat_native_snake_alpha_diagram K C S C1 t T T0
  P A B X D b c h)) B) (λ v : τ (@Transf K C A B), (@comp_fapp0 (Functor_cat K C)
  (@kernel_adjunction_family_func K C S t T P (@one_cat_native_snake_alpha_diagram K C S C1 t T T0 P A B X D b c
  h)) A B v (@kernel_adjunction_family_inclusion_transf K C S t T P (@one_cat_native_snake_alpha_diagram K C S
  C1 t T T0 P A B X D b c h)))) _ _ (@one_cat_square_family_src_path K C C1 A B (@kernel_adjunction_family_func
  K C S t T P (@transf_arrow_diagram_func K C X D c)) X (@one_cat_native_snake_alpha K C S C1 t T T0 P A B X D b
  c h) b (@native_snake_incoming K C t T A B X D b c h) (@kernel_adjunction_family_inclusion_transf K C S t T P
  (@transf_arrow_diagram_func K C X D c)) (@one_cat_native_snake_alpha_reconstruction K C S C1 t T T0 P A B X D
  b c h))));

// Kernel action reconstructs the original source map of the second square.
symbol one_cat_native_snake_kernel_second_reconstruction [K C : Cat] [S : τ (@PreadditiveCategory C)]
  (C1 : τ (IsNCat (cat_succ cat_zero) C)) [t : τ (Obj C)]
  (T : τ (@TerminalObject C t)) (T0 : τ (@TerminalObject (Op_cat C) t))
  (P : τ (@KernelAdjunctionStructure C S t T)) (Q : τ (@CokernelAdjunctionStructure C S t T0))
  [A B X D : τ (Functor K C)] (b : τ (@Transf K C B X)) (c : τ (@Transf K C X D))
  (h : τ (@NativeSnakeInput K C t T A B X D b c))
  : τ (@= (@Transf K C (@kernel_adjunction_family_func K C S t T P (@transf_arrow_diagram_func K C B X b))
    (@cokernel_adjunction_family_func K C S t T0 Q (@native_snake_incoming_diagram K C t T A B X D b c h)))
    (@comp_fapp0 (Functor_cat K C) (@kernel_adjunction_family_func K C S t T P (@transf_arrow_diagram_func K C B
    X b)) (@kernel_adjunction_family_func K C S t T P (@one_cat_native_snake_gamma_diagram K C S C1 t T T0 Q A B
    X D b c h)) (@cokernel_adjunction_family_func K C S t T0 Q (@native_snake_incoming_diagram K C t T A B X D b
    c h)) (@kernel_adjunction_family_inclusion_transf K C S t T P (@one_cat_native_snake_gamma_diagram K C S C1
    t T T0 Q A B X D b c h)) (@one_cat_native_snake_kernel_second K C S C1 t T T0 P Q A B X D b c h))
    (@comp_fapp0 (Functor_cat K C) (@kernel_adjunction_family_func K C S t T P (@transf_arrow_diagram_func K C B
    X b)) B (@cokernel_adjunction_family_func K C S t T0 Q (@native_snake_incoming_diagram K C t T A B X D b c
    h)) (@cokernel_adjunction_family_projection_transf K C S t T0 Q (@native_snake_incoming_diagram K C t T A B
    X D b c h)) (@kernel_adjunction_family_inclusion_transf K C S t T P (@transf_arrow_diagram_func K C B X
    b))))
≔ (@eq_trans _ _ _ _ (@one_cat_kernel_family_map_inclusion_path K C S C1 t T T0 P Q (@transf_arrow_diagram_func
  K C B X b) (@one_cat_native_snake_gamma_diagram K C S C1 t T T0 Q A B X D b c h)
  (@one_cat_native_snake_second_diagram_map K C S C1 t T T0 P Q A B X D b c h)) (@eq_ap (@Transf K C B
  (@cokernel_adjunction_family_func K C S t T0 Q (@native_snake_incoming_diagram K C t T A B X D b c h)))
  (@Transf K C (@kernel_adjunction_family_func K C S t T P (@transf_arrow_diagram_func K C B X b))
  (@cokernel_adjunction_family_func K C S t T0 Q (@native_snake_incoming_diagram K C t T A B X D b c h))) (λ v :
  τ (@Transf K C B (@cokernel_adjunction_family_func K C S t T0 Q (@native_snake_incoming_diagram K C t T A B X
  D b c h))), (@comp_fapp0 (Functor_cat K C) (@kernel_adjunction_family_func K C S t T P
  (@transf_arrow_diagram_func K C B X b)) B (@cokernel_adjunction_family_func K C S t T0 Q
  (@native_snake_incoming_diagram K C t T A B X D b c h)) v (@kernel_adjunction_family_inclusion_transf K C S t
  T P (@transf_arrow_diagram_func K C B X b)))) _ _ (@one_cat_square_family_src_path K C C1 B
  (@cokernel_adjunction_family_func K C S t T0 Q (@native_snake_incoming_diagram K C t T A B X D b c h)) X D b
  (@one_cat_native_snake_gamma K C S C1 t T T0 Q A B X D b c h) (@cokernel_adjunction_family_projection_transf K
  C S t T0 Q (@native_snake_incoming_diagram K C t T A B X D b c h)) c (@eq_sym _ _ _
  (@one_cat_native_snake_gamma_reconstruction K C S C1 t T T0 Q A B X D b c h)))));

// Cokernel action reconstructs the original target map of the first square.
symbol one_cat_native_snake_cokernel_first_reconstruction [K C : Cat] [S : τ (@PreadditiveCategory C)]
  (C1 : τ (IsNCat (cat_succ cat_zero) C)) [t : τ (Obj C)]
  (T : τ (@TerminalObject C t)) (T0 : τ (@TerminalObject (Op_cat C) t))
  (P : τ (@KernelAdjunctionStructure C S t T)) (Q : τ (@CokernelAdjunctionStructure C S t T0))
  [A B X D : τ (Functor K C)] (b : τ (@Transf K C B X)) (c : τ (@Transf K C X D))
  (h : τ (@NativeSnakeInput K C t T A B X D b c))
  : τ (@= (@Transf K C (@kernel_adjunction_family_func K C S t T P (@transf_arrow_diagram_func K C X D c))
    (@cokernel_adjunction_family_func K C S t T0 Q (@transf_arrow_diagram_func K C B X b))) (@comp_fapp0
    (Functor_cat K C) (@kernel_adjunction_family_func K C S t T P (@transf_arrow_diagram_func K C X D c))
    (@cokernel_adjunction_family_func K C S t T0 Q (@one_cat_native_snake_alpha_diagram K C S C1 t T T0 P A B X
    D b c h)) (@cokernel_adjunction_family_func K C S t T0 Q (@transf_arrow_diagram_func K C B X b))
    (@one_cat_native_snake_cokernel_first K C S C1 t T T0 P Q A B X D b c h)
    (@cokernel_adjunction_family_projection_transf K C S t T0 Q (@one_cat_native_snake_alpha_diagram K C S C1 t
    T T0 P A B X D b c h))) (@comp_fapp0 (Functor_cat K C) (@kernel_adjunction_family_func K C S t T P
    (@transf_arrow_diagram_func K C X D c)) X (@cokernel_adjunction_family_func K C S t T0 Q
    (@transf_arrow_diagram_func K C B X b)) (@cokernel_adjunction_family_projection_transf K C S t T0 Q
    (@transf_arrow_diagram_func K C B X b)) (@kernel_adjunction_family_inclusion_transf K C S t T P
    (@transf_arrow_diagram_func K C X D c))))
≔ (@eq_trans _ _ _ _ (@one_cat_cokernel_family_map_projection_path K C S C1 t T T0 P Q
  (@one_cat_native_snake_alpha_diagram K C S C1 t T T0 P A B X D b c h) (@transf_arrow_diagram_func K C B X b)
  (@one_cat_native_snake_first_diagram_map K C S C1 t T T0 P Q A B X D b c h)) (@eq_ap (@Transf K C
  (@kernel_adjunction_family_func K C S t T P (@transf_arrow_diagram_func K C X D c)) X) (@Transf K C
  (@kernel_adjunction_family_func K C S t T P (@transf_arrow_diagram_func K C X D c))
  (@cokernel_adjunction_family_func K C S t T0 Q (@transf_arrow_diagram_func K C B X b))) (λ v : τ (@Transf K C
  (@kernel_adjunction_family_func K C S t T P (@transf_arrow_diagram_func K C X D c)) X), (@comp_fapp0
  (Functor_cat K C) (@kernel_adjunction_family_func K C S t T P (@transf_arrow_diagram_func K C X D c)) X
  (@cokernel_adjunction_family_func K C S t T0 Q (@transf_arrow_diagram_func K C B X b))
  (@cokernel_adjunction_family_projection_transf K C S t T0 Q (@transf_arrow_diagram_func K C B X b)) v)) _ _
  (@one_cat_square_family_tgt_path K C C1 A B (@kernel_adjunction_family_func K C S t T P
  (@transf_arrow_diagram_func K C X D c)) X (@one_cat_native_snake_alpha K C S C1 t T T0 P A B X D b c h) b
  (@native_snake_incoming K C t T A B X D b c h) (@kernel_adjunction_family_inclusion_transf K C S t T P
  (@transf_arrow_diagram_func K C X D c)) (@one_cat_native_snake_alpha_reconstruction K C S C1 t T T0 P A B X D
  b c h))));

// Cokernel action reconstructs the original target map of the second square.
symbol one_cat_native_snake_cokernel_second_reconstruction [K C : Cat] [S : τ (@PreadditiveCategory C)]
  (C1 : τ (IsNCat (cat_succ cat_zero) C)) [t : τ (Obj C)]
  (T : τ (@TerminalObject C t)) (T0 : τ (@TerminalObject (Op_cat C) t))
  (P : τ (@KernelAdjunctionStructure C S t T)) (Q : τ (@CokernelAdjunctionStructure C S t T0))
  [A B X D : τ (Functor K C)] (b : τ (@Transf K C B X)) (c : τ (@Transf K C X D))
  (h : τ (@NativeSnakeInput K C t T A B X D b c))
  : τ (@= (@Transf K C X (@cokernel_adjunction_family_func K C S t T0 Q (@one_cat_native_snake_gamma_diagram K C
    S C1 t T T0 Q A B X D b c h))) (@comp_fapp0 (Functor_cat K C) X (@cokernel_adjunction_family_func K C S t T0
    Q (@transf_arrow_diagram_func K C B X b)) (@cokernel_adjunction_family_func K C S t T0 Q
    (@one_cat_native_snake_gamma_diagram K C S C1 t T T0 Q A B X D b c h))
    (@one_cat_native_snake_cokernel_second K C S C1 t T T0 P Q A B X D b c h)
    (@cokernel_adjunction_family_projection_transf K C S t T0 Q (@transf_arrow_diagram_func K C B X b)))
    (@comp_fapp0 (Functor_cat K C) X D (@cokernel_adjunction_family_func K C S t T0 Q
    (@one_cat_native_snake_gamma_diagram K C S C1 t T T0 Q A B X D b c h))
    (@cokernel_adjunction_family_projection_transf K C S t T0 Q (@one_cat_native_snake_gamma_diagram K C S C1 t
    T T0 Q A B X D b c h)) c))
≔ (@eq_trans _ _ _ _ (@one_cat_cokernel_family_map_projection_path K C S C1 t T T0 P Q
  (@transf_arrow_diagram_func K C B X b) (@one_cat_native_snake_gamma_diagram K C S C1 t T T0 Q A B X D b c h)
  (@one_cat_native_snake_second_diagram_map K C S C1 t T T0 P Q A B X D b c h)) (@eq_ap (@Transf K C X D)
  (@Transf K C X (@cokernel_adjunction_family_func K C S t T0 Q (@one_cat_native_snake_gamma_diagram K C S C1 t
  T T0 Q A B X D b c h))) (λ v : τ (@Transf K C X D), (@comp_fapp0 (Functor_cat K C) X D
  (@cokernel_adjunction_family_func K C S t T0 Q (@one_cat_native_snake_gamma_diagram K C S C1 t T T0 Q A B X D
  b c h)) (@cokernel_adjunction_family_projection_transf K C S t T0 Q (@one_cat_native_snake_gamma_diagram K C S
  C1 t T T0 Q A B X D b c h)) v)) _ _ (@one_cat_square_family_tgt_path K C C1 B
  (@cokernel_adjunction_family_func K C S t T0 Q (@native_snake_incoming_diagram K C t T A B X D b c h)) X D b
  (@one_cat_native_snake_gamma K C S C1 t T T0 Q A B X D b c h) (@cokernel_adjunction_family_projection_transf K
  C S t T0 Q (@native_snake_incoming_diagram K C t T A B X D b c h)) c (@eq_sym _ _ _
  (@one_cat_native_snake_gamma_reconstruction K C S C1 t T T0 Q A B X D b c h)))));
