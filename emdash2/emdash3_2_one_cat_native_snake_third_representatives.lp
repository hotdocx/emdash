/* Whole E representatives for the third canonical snake comparison. */
require open emdash.emdash3_2_one_cat_native_snake_third_covers;

// The original source-image factor and both cover projections reconstruct bx=κ_cps.
symbol one_cat_native_snake_third_middle_representative_path [K C : Cat]
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
  h) X) (@comp_fapp0 (Functor_cat K C) (@one_cat_native_snake_third_middle_cover_source K C C1 Prod t Add T0 P Q
  N A B X D b c h) B X b (@one_cat_native_snake_third_middle_cover_second K C C1 Prod t Add T0 P Q N A B X D b c
  h)) (@comp_fapp0 (Functor_cat K C) (@one_cat_native_snake_third_middle_cover_source K C C1 Prod t Add T0 P Q N
  A B X D b c h) (@kernel_adjunction_family_func K C (@additive_preadditive C Prod t Add) t
  (@additive_terminal_object C Prod t Add) P (@transf_arrow_diagram_func K C X D c)) X
  (@kernel_adjunction_family_inclusion_transf K C (@additive_preadditive C Prod t Add) t
  (@additive_terminal_object C Prod t Add) P (@transf_arrow_diagram_func K C X D c)) (@comp_fapp0 (Functor_cat K
  C) (@one_cat_native_snake_third_middle_cover_source K C C1 Prod t Add T0 P Q N A B X D b c h)
  (@one_cat_native_snake_third_cover_source K C C1 Prod t Add T0 P Q N A B X D b c h)
  (@kernel_adjunction_family_func K C (@additive_preadditive C Prod t Add) t (@additive_terminal_object C Prod t
  Add) P (@transf_arrow_diagram_func K C X D c)) (@one_cat_native_snake_third_cover_lift K C C1 Prod t Add T0 P
  Q N A B X D b c h) (@one_cat_native_snake_third_middle_cover_first K C C1 Prod t Add T0 P Q N A B X D b c
  h))))
≔ (@eq_trans _ _ _ _ (@eq_ap (@Transf K C B X) (@Transf K C (@one_cat_native_snake_third_middle_cover_source K C
  C1 Prod t Add T0 P Q N A B X D b c h) X) (λ v : τ (@Transf K C B X), (@comp_fapp0 (Functor_cat K C)
  (@one_cat_native_snake_third_middle_cover_source K C C1 Prod t Add T0 P Q N A B X D b c h) B X v
  (@one_cat_native_snake_third_middle_cover_second K C C1 Prod t Add T0 P Q N A B X D b c h))) _ _ (@eq_sym _ _
  _ (@one_cat_image_family_source_factor_path K C (@additive_preadditive C Prod t Add) C1 t
  (@additive_terminal_object C Prod t Add) T0 P Q (@transf_arrow_diagram_func K C B X b)))) (@eq_trans _ _ _ _
  (@eq_sym _ _ _ (@comp_assoc (Functor_cat K C) (@one_cat_native_snake_third_middle_cover_source K C C1 Prod t
  Add T0 P Q N A B X D b c h) B (@comp_cat_fapp0 K (Functor_cat WalkingArrow_cat C) C (@adjunction_image_func C
  (@additive_preadditive C Prod t Add) t (@additive_terminal_object C Prod t Add) T0 P Q)
  (@transf_arrow_diagram_func K C B X b)) X (@kernel_adjunction_family_inclusion_transf K C
  (@additive_preadditive C Prod t Add) t (@additive_terminal_object C Prod t Add) P (@comp_cat_fapp0 K
  (Functor_cat WalkingArrow_cat C) (Functor_cat WalkingArrow_cat C) (@cokernel_adjunction_arrow_func C
  (@additive_preadditive C Prod t Add) t T0 Q) (@transf_arrow_diagram_func K C B X b)))
  (@one_cat_image_family_source_transf K C (@additive_preadditive C Prod t Add) C1 t (@additive_terminal_object
  C Prod t Add) T0 P Q (@transf_arrow_diagram_func K C B X b)) (@one_cat_native_snake_third_middle_cover_second
  K C C1 Prod t Add T0 P Q N A B X D b c h))) (@eq_trans _ _ _ _ (@eq_ap (@Transf K C
  (@one_cat_native_snake_third_middle_cover_source K C C1 Prod t Add T0 P Q N A B X D b c h) (@comp_cat_fapp0 K
  (Functor_cat WalkingArrow_cat C) C (@adjunction_image_func C (@additive_preadditive C Prod t Add) t
  (@additive_terminal_object C Prod t Add) T0 P Q) (@transf_arrow_diagram_func K C B X b))) (@Transf K C
  (@one_cat_native_snake_third_middle_cover_source K C C1 Prod t Add T0 P Q N A B X D b c h) X) (λ v : τ
  (@Transf K C (@one_cat_native_snake_third_middle_cover_source K C C1 Prod t Add T0 P Q N A B X D b c h)
  (@comp_cat_fapp0 K (Functor_cat WalkingArrow_cat C) C (@adjunction_image_func C (@additive_preadditive C Prod
  t Add) t (@additive_terminal_object C Prod t Add) T0 P Q) (@transf_arrow_diagram_func K C B X b))),
  (@comp_fapp0 (Functor_cat K C) (@one_cat_native_snake_third_middle_cover_source K C C1 Prod t Add T0 P Q N A B
  X D b c h) (@comp_cat_fapp0 K (Functor_cat WalkingArrow_cat C) C (@adjunction_image_func C
  (@additive_preadditive C Prod t Add) t (@additive_terminal_object C Prod t Add) T0 P Q)
  (@transf_arrow_diagram_func K C B X b)) X (@kernel_adjunction_family_inclusion_transf K C
  (@additive_preadditive C Prod t Add) t (@additive_terminal_object C Prod t Add) P (@comp_cat_fapp0 K
  (Functor_cat WalkingArrow_cat C) (Functor_cat WalkingArrow_cat C) (@cokernel_adjunction_arrow_func C
  (@additive_preadditive C Prod t Add) t T0 Q) (@transf_arrow_diagram_func K C B X b))) v)) _ _ (@eq_sym _ _ _
  (@one_cat_native_snake_third_middle_cover_compatibility K C C1 Prod t Add T0 P Q N A B X D b c h))) (@eq_trans
  _ _ _ _ (@comp_assoc (Functor_cat K C) (@one_cat_native_snake_third_middle_cover_source K C C1 Prod t Add T0 P
  Q N A B X D b c h) (@one_cat_native_snake_third_cover_source K C C1 Prod t Add T0 P Q N A B X D b c h)
  (@comp_cat_fapp0 K (Functor_cat WalkingArrow_cat C) C (@adjunction_image_func C (@additive_preadditive C Prod
  t Add) t (@additive_terminal_object C Prod t Add) T0 P Q) (@transf_arrow_diagram_func K C B X b)) X
  (@kernel_adjunction_family_inclusion_transf K C (@additive_preadditive C Prod t Add) t
  (@additive_terminal_object C Prod t Add) P (@comp_cat_fapp0 K (Functor_cat WalkingArrow_cat C) (Functor_cat
  WalkingArrow_cat C) (@cokernel_adjunction_arrow_func C (@additive_preadditive C Prod t Add) t T0 Q)
  (@transf_arrow_diagram_func K C B X b))) (@one_cat_native_snake_third_cover_image_lift K C C1 Prod t Add T0 P
  Q N A B X D b c h) (@one_cat_native_snake_third_middle_cover_first K C C1 Prod t Add T0 P Q N A B X D b c h))
  (@eq_trans _ _ _ _ (@eq_ap (@Transf K C (@one_cat_native_snake_third_cover_source K C C1 Prod t Add T0 P Q N A
  B X D b c h) X) (@Transf K C (@one_cat_native_snake_third_middle_cover_source K C C1 Prod t Add T0 P Q N A B X
  D b c h) X) (λ v : τ (@Transf K C (@one_cat_native_snake_third_cover_source K C C1 Prod t Add T0 P Q N A B X D
  b c h) X), (@comp_fapp0 (Functor_cat K C) (@one_cat_native_snake_third_middle_cover_source K C C1 Prod t Add
  T0 P Q N A B X D b c h) (@one_cat_native_snake_third_cover_source K C C1 Prod t Add T0 P Q N A B X D b c h) X
  v (@one_cat_native_snake_third_middle_cover_first K C C1 Prod t Add T0 P Q N A B X D b c h))) _ _
  (@one_cat_native_snake_third_cover_image_reconstruction K C C1 Prod t Add T0 P Q N A B X D b c h)) (@eq_sym _
  _ _ (@comp_assoc (Functor_cat K C) (@one_cat_native_snake_third_middle_cover_source K C C1 Prod t Add T0 P Q N
  A B X D b c h) (@one_cat_native_snake_third_cover_source K C C1 Prod t Add T0 P Q N A B X D b c h)
  (@kernel_adjunction_family_func K C (@additive_preadditive C Prod t Add) t (@additive_terminal_object C Prod t
  Add) P (@transf_arrow_diagram_func K C X D c)) X (@kernel_adjunction_family_inclusion_transf K C
  (@additive_preadditive C Prod t Add) t (@additive_terminal_object C Prod t Add) P (@transf_arrow_diagram_func
  K C X D c)) (@one_cat_native_snake_third_cover_lift K C C1 Prod t Add T0 P Q N A B X D b c h)
  (@one_cat_native_snake_third_middle_cover_first K C C1 Prod t Add T0 P Q N A B X D b c h))))))));

// The original γπ_a=cb reconstruction shows that x is killed by the E differential.
symbol one_cat_native_snake_third_cover_kernel_zero [K C : Cat]
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
  h) D) (@comp_fapp0 (Functor_cat K C) (@one_cat_native_snake_third_middle_cover_source K C C1 Prod t Add T0 P Q
  N A B X D b c h) B D (@comp_fapp0 (Functor_cat K C) B (@cokernel_adjunction_family_func K C
  (@additive_preadditive C Prod t Add) t T0 Q (@native_snake_incoming_diagram K C t (@additive_terminal_object C
  Prod t Add) A B X D b c h)) D (@one_cat_native_snake_gamma K C (@additive_preadditive C Prod t Add) C1 t
  (@additive_terminal_object C Prod t Add) T0 Q A B X D b c h) (@cokernel_adjunction_family_projection_transf K
  C (@additive_preadditive C Prod t Add) t T0 Q (@native_snake_incoming_diagram K C t (@additive_terminal_object
  C Prod t Add) A B X D b c h))) (@one_cat_native_snake_third_middle_cover_second K C C1 Prod t Add T0 P Q N A B
  X D b c h)) (@zero_arrow_family_zero_transf K C t (@additive_terminal_object C Prod t Add) T0
  (@one_cat_native_snake_third_middle_cover_source K C C1 Prod t Add T0 P Q N A B X D b c h) D))
≔ (@eq_trans _ _ _ _ (@eq_ap (@Transf K C B D) (@Transf K C (@one_cat_native_snake_third_middle_cover_source K C
  C1 Prod t Add T0 P Q N A B X D b c h) D) (λ v : τ (@Transf K C B D), (@comp_fapp0 (Functor_cat K C)
  (@one_cat_native_snake_third_middle_cover_source K C C1 Prod t Add T0 P Q N A B X D b c h) B D v
  (@one_cat_native_snake_third_middle_cover_second K C C1 Prod t Add T0 P Q N A B X D b c h))) _ _
  (@one_cat_native_snake_gamma_reconstruction K C (@additive_preadditive C Prod t Add) C1 t
  (@additive_terminal_object C Prod t Add) T0 Q A B X D b c h)) (@eq_trans _ _ _ _ (@eq_sym _ _ _ (@comp_assoc
  (Functor_cat K C) (@one_cat_native_snake_third_middle_cover_source K C C1 Prod t Add T0 P Q N A B X D b c h) B
  X D c b (@one_cat_native_snake_third_middle_cover_second K C C1 Prod t Add T0 P Q N A B X D b c h)))
  (@eq_trans _ _ _ _ (@eq_ap (@Transf K C (@one_cat_native_snake_third_middle_cover_source K C C1 Prod t Add T0
  P Q N A B X D b c h) X) (@Transf K C (@one_cat_native_snake_third_middle_cover_source K C C1 Prod t Add T0 P Q
  N A B X D b c h) D) (λ v : τ (@Transf K C (@one_cat_native_snake_third_middle_cover_source K C C1 Prod t Add
  T0 P Q N A B X D b c h) X), (@comp_fapp0 (Functor_cat K C) (@one_cat_native_snake_third_middle_cover_source K
  C C1 Prod t Add T0 P Q N A B X D b c h) X D c v)) _ _ (@one_cat_native_snake_third_middle_representative_path
  K C C1 Prod t Add T0 P Q N A B X D b c h)) (@eq_trans _ _ _ _ (@comp_assoc (Functor_cat K C)
  (@one_cat_native_snake_third_middle_cover_source K C C1 Prod t Add T0 P Q N A B X D b c h)
  (@kernel_adjunction_family_func K C (@additive_preadditive C Prod t Add) t (@additive_terminal_object C Prod t
  Add) P (@transf_arrow_diagram_func K C X D c)) X D c (@kernel_adjunction_family_inclusion_transf K C
  (@additive_preadditive C Prod t Add) t (@additive_terminal_object C Prod t Add) P (@transf_arrow_diagram_func
  K C X D c)) (@comp_fapp0 (Functor_cat K C) (@one_cat_native_snake_third_middle_cover_source K C C1 Prod t Add
  T0 P Q N A B X D b c h) (@one_cat_native_snake_third_cover_source K C C1 Prod t Add T0 P Q N A B X D b c h)
  (@kernel_adjunction_family_func K C (@additive_preadditive C Prod t Add) t (@additive_terminal_object C Prod t
  Add) P (@transf_arrow_diagram_func K C X D c)) (@one_cat_native_snake_third_cover_lift K C C1 Prod t Add T0 P
  Q N A B X D b c h) (@one_cat_native_snake_third_middle_cover_first K C C1 Prod t Add T0 P Q N A B X D b c h)))
  (@eq_trans _ _ _ _ (@eq_ap (@Transf K C (@kernel_adjunction_family_func K C (@additive_preadditive C Prod t
  Add) t (@additive_terminal_object C Prod t Add) P (@transf_arrow_diagram_func K C X D c)) D) (@Transf K C
  (@one_cat_native_snake_third_middle_cover_source K C C1 Prod t Add T0 P Q N A B X D b c h) D) (λ v : τ
  (@Transf K C (@kernel_adjunction_family_func K C (@additive_preadditive C Prod t Add) t
  (@additive_terminal_object C Prod t Add) P (@transf_arrow_diagram_func K C X D c)) D), (@comp_fapp0
  (Functor_cat K C) (@one_cat_native_snake_third_middle_cover_source K C C1 Prod t Add T0 P Q N A B X D b c h)
  (@kernel_adjunction_family_func K C (@additive_preadditive C Prod t Add) t (@additive_terminal_object C Prod t
  Add) P (@transf_arrow_diagram_func K C X D c)) D v (@comp_fapp0 (Functor_cat K C)
  (@one_cat_native_snake_third_middle_cover_source K C C1 Prod t Add T0 P Q N A B X D b c h)
  (@one_cat_native_snake_third_cover_source K C C1 Prod t Add T0 P Q N A B X D b c h)
  (@kernel_adjunction_family_func K C (@additive_preadditive C Prod t Add) t (@additive_terminal_object C Prod t
  Add) P (@transf_arrow_diagram_func K C X D c)) (@one_cat_native_snake_third_cover_lift K C C1 Prod t Add T0 P
  Q N A B X D b c h) (@one_cat_native_snake_third_middle_cover_first K C C1 Prod t Add T0 P Q N A B X D b c
  h)))) _ _ (@one_cat_kernel_family_annihilation_path K C (@additive_preadditive C Prod t Add) C1 t
  (@additive_terminal_object C Prod t Add) T0 P (@transf_arrow_diagram_func K C X D c)))
  (@one_cat_zero_family_precompose_path K C C1 t (@additive_terminal_object C Prod t Add) T0
  (@one_cat_native_snake_third_middle_cover_source K C C1 Prod t Add T0 P Q N A B X D b c h)
  (@kernel_adjunction_family_func K C (@additive_preadditive C Prod t Add) t (@additive_terminal_object C Prod t
  Add) P (@transf_arrow_diagram_func K C X D c)) D (@comp_fapp0 (Functor_cat K C)
  (@one_cat_native_snake_third_middle_cover_source K C C1 Prod t Add T0 P Q N A B X D b c h)
  (@one_cat_native_snake_third_cover_source K C C1 Prod t Add T0 P Q N A B X D b c h)
  (@kernel_adjunction_family_func K C (@additive_preadditive C Prod t Add) t (@additive_terminal_object C Prod t
  Add) P (@transf_arrow_diagram_func K C X D c)) (@one_cat_native_snake_third_cover_lift K C C1 Prod t Add T0 P
  Q N A B X D b c h) (@one_cat_native_snake_third_middle_cover_first K C C1 Prod t Add T0 P Q N A B X D b c
  h))))))));

// The original native kernel mate lifts x into the same E used by ∂.
symbol one_cat_native_snake_third_cover_kernel_lift [K C : Cat]
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
  (@one_cat_native_snake_cover_source K C (@additive_preadditive C Prod t Add) C1 t (@additive_terminal_object C
  Prod t Add) T0 P Q A B X D b c h))
≔ (@one_cat_kernel_family_lift K C (@additive_preadditive C Prod t Add) C1 t (@additive_terminal_object C Prod t
  Add) T0 P (@one_cat_native_snake_third_middle_cover_source K C C1 Prod t Add T0 P Q N A B X D b c h)
  (@precomposed_diagram_family_func K C B (@one_cat_native_snake_gamma_diagram K C (@additive_preadditive C Prod
  t Add) C1 t (@additive_terminal_object C Prod t Add) T0 Q A B X D b c h)
  (@cokernel_adjunction_family_projection_transf K C (@additive_preadditive C Prod t Add) t T0 Q
  (@native_snake_incoming_diagram K C t (@additive_terminal_object C Prod t Add) A B X D b c h)))
  (@one_cat_native_snake_third_middle_cover_second K C C1 Prod t Add T0 P Q N A B X D b c h)
  (@one_cat_native_snake_third_cover_kernel_zero K C C1 Prod t Add T0 P Q N A B X D b c h));

// The original inclusion j:E⇒B reconstructs x.
symbol one_cat_native_snake_third_cover_kernel_reconstruction [K C : Cat]
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
  h) B) (@comp_fapp0 (Functor_cat K C) (@one_cat_native_snake_third_middle_cover_source K C C1 Prod t Add T0 P Q
  N A B X D b c h) (@one_cat_native_snake_cover_source K C (@additive_preadditive C Prod t Add) C1 t
  (@additive_terminal_object C Prod t Add) T0 P Q A B X D b c h) B (@one_cat_native_snake_cover_first K C
  (@additive_preadditive C Prod t Add) C1 t (@additive_terminal_object C Prod t Add) T0 P Q A B X D b c h)
  (@one_cat_native_snake_third_cover_kernel_lift K C C1 Prod t Add T0 P Q N A B X D b c h))
  (@one_cat_native_snake_third_middle_cover_second K C C1 Prod t Add T0 P Q N A B X D b c h))
≔ (@one_cat_kernel_family_lift_ambient_reconstruction K C (@additive_preadditive C Prod t Add) C1 t
  (@additive_terminal_object C Prod t Add) T0 P (@one_cat_native_snake_third_middle_cover_source K C C1 Prod t
  Add T0 P Q N A B X D b c h) (@precomposed_diagram_family_func K C B (@one_cat_native_snake_gamma_diagram K C
  (@additive_preadditive C Prod t Add) C1 t (@additive_terminal_object C Prod t Add) T0 Q A B X D b c h)
  (@cokernel_adjunction_family_projection_transf K C (@additive_preadditive C Prod t Add) t T0 Q
  (@native_snake_incoming_diagram K C t (@additive_terminal_object C Prod t Add) A B X D b c h)))
  (@one_cat_native_snake_third_middle_cover_second K C C1 Prod t Add T0 P Q N A B X D b c h)
  (@one_cat_native_snake_third_cover_kernel_zero K C C1 Prod t Add T0 P Q N A B X D b c h));

// Original kernel cancellation identifies ℓw with ps in K(c).
symbol one_cat_native_snake_third_left_cycle_path [K C : Cat]
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
  h) (@kernel_adjunction_family_func K C (@additive_preadditive C Prod t Add) t (@additive_terminal_object C
  Prod t Add) P (@transf_arrow_diagram_func K C X D c))) (@comp_fapp0 (Functor_cat K C)
  (@one_cat_native_snake_third_middle_cover_source K C C1 Prod t Add T0 P Q N A B X D b c h)
  (@one_cat_native_snake_cover_source K C (@additive_preadditive C Prod t Add) C1 t (@additive_terminal_object C
  Prod t Add) T0 P Q A B X D b c h) (@kernel_adjunction_family_func K C (@additive_preadditive C Prod t Add) t
  (@additive_terminal_object C Prod t Add) P (@transf_arrow_diagram_func K C X D c))
  (@one_cat_native_snake_covered_lift K C (@additive_preadditive C Prod t Add) C1 t (@additive_terminal_object C
  Prod t Add) T0 P Q A B X D b c h) (@one_cat_native_snake_third_cover_kernel_lift K C C1 Prod t Add T0 P Q N A
  B X D b c h)) (@comp_fapp0 (Functor_cat K C) (@one_cat_native_snake_third_middle_cover_source K C C1 Prod t
  Add T0 P Q N A B X D b c h) (@one_cat_native_snake_third_cover_source K C C1 Prod t Add T0 P Q N A B X D b c
  h) (@kernel_adjunction_family_func K C (@additive_preadditive C Prod t Add) t (@additive_terminal_object C
  Prod t Add) P (@transf_arrow_diagram_func K C X D c)) (@one_cat_native_snake_third_cover_lift K C C1 Prod t
  Add T0 P Q N A B X D b c h) (@one_cat_native_snake_third_middle_cover_first K C C1 Prod t Add T0 P Q N A B X D
  b c h)))
≔ (@one_cat_kernel_family_inclusion_reflect_path K C (@additive_preadditive C Prod t Add) C1 t
  (@additive_terminal_object C Prod t Add) T0 P (@one_cat_native_snake_third_middle_cover_source K C C1 Prod t
  Add T0 P Q N A B X D b c h) (@transf_arrow_diagram_func K C X D c) (@comp_fapp0 (Functor_cat K C)
  (@one_cat_native_snake_third_middle_cover_source K C C1 Prod t Add T0 P Q N A B X D b c h)
  (@one_cat_native_snake_cover_source K C (@additive_preadditive C Prod t Add) C1 t (@additive_terminal_object C
  Prod t Add) T0 P Q A B X D b c h) (@kernel_adjunction_family_func K C (@additive_preadditive C Prod t Add) t
  (@additive_terminal_object C Prod t Add) P (@transf_arrow_diagram_func K C X D c))
  (@one_cat_native_snake_covered_lift K C (@additive_preadditive C Prod t Add) C1 t (@additive_terminal_object C
  Prod t Add) T0 P Q A B X D b c h) (@one_cat_native_snake_third_cover_kernel_lift K C C1 Prod t Add T0 P Q N A
  B X D b c h)) (@comp_fapp0 (Functor_cat K C) (@one_cat_native_snake_third_middle_cover_source K C C1 Prod t
  Add T0 P Q N A B X D b c h) (@one_cat_native_snake_third_cover_source K C C1 Prod t Add T0 P Q N A B X D b c
  h) (@kernel_adjunction_family_func K C (@additive_preadditive C Prod t Add) t (@additive_terminal_object C
  Prod t Add) P (@transf_arrow_diagram_func K C X D c)) (@one_cat_native_snake_third_cover_lift K C C1 Prod t
  Add T0 P Q N A B X D b c h) (@one_cat_native_snake_third_middle_cover_first K C C1 Prod t Add T0 P Q N A B X D
  b c h)) (@eq_trans _ _ _ _ (@comp_assoc (Functor_cat K C) (@one_cat_native_snake_third_middle_cover_source K C
  C1 Prod t Add T0 P Q N A B X D b c h) (@one_cat_native_snake_cover_source K C (@additive_preadditive C Prod t
  Add) C1 t (@additive_terminal_object C Prod t Add) T0 P Q A B X D b c h) (@kernel_adjunction_family_func K C
  (@additive_preadditive C Prod t Add) t (@additive_terminal_object C Prod t Add) P (@transf_arrow_diagram_func
  K C X D c)) X (@kernel_adjunction_family_inclusion_transf K C (@additive_preadditive C Prod t Add) t
  (@additive_terminal_object C Prod t Add) P (@transf_arrow_diagram_func K C X D c))
  (@one_cat_native_snake_covered_lift K C (@additive_preadditive C Prod t Add) C1 t (@additive_terminal_object C
  Prod t Add) T0 P Q A B X D b c h) (@one_cat_native_snake_third_cover_kernel_lift K C C1 Prod t Add T0 P Q N A
  B X D b c h)) (@eq_trans _ _ _ _ (@eq_ap (@Transf K C (@one_cat_native_snake_cover_source K C
  (@additive_preadditive C Prod t Add) C1 t (@additive_terminal_object C Prod t Add) T0 P Q A B X D b c h) X)
  (@Transf K C (@one_cat_native_snake_third_middle_cover_source K C C1 Prod t Add T0 P Q N A B X D b c h) X) (λ
  v : τ (@Transf K C (@one_cat_native_snake_cover_source K C (@additive_preadditive C Prod t Add) C1 t
  (@additive_terminal_object C Prod t Add) T0 P Q A B X D b c h) X), (@comp_fapp0 (Functor_cat K C)
  (@one_cat_native_snake_third_middle_cover_source K C C1 Prod t Add T0 P Q N A B X D b c h)
  (@one_cat_native_snake_cover_source K C (@additive_preadditive C Prod t Add) C1 t (@additive_terminal_object C
  Prod t Add) T0 P Q A B X D b c h) X v (@one_cat_native_snake_third_cover_kernel_lift K C C1 Prod t Add T0 P Q
  N A B X D b c h))) _ _ (@one_cat_native_snake_covered_lift_reconstruction K C (@additive_preadditive C Prod t
  Add) C1 t (@additive_terminal_object C Prod t Add) T0 P Q A B X D b c h)) (@eq_trans _ _ _ _ (@eq_sym _ _ _
  (@comp_assoc (Functor_cat K C) (@one_cat_native_snake_third_middle_cover_source K C C1 Prod t Add T0 P Q N A B
  X D b c h) (@one_cat_native_snake_cover_source K C (@additive_preadditive C Prod t Add) C1 t
  (@additive_terminal_object C Prod t Add) T0 P Q A B X D b c h) B X b (@one_cat_native_snake_cover_first K C
  (@additive_preadditive C Prod t Add) C1 t (@additive_terminal_object C Prod t Add) T0 P Q A B X D b c h)
  (@one_cat_native_snake_third_cover_kernel_lift K C C1 Prod t Add T0 P Q N A B X D b c h))) (@eq_trans _ _ _ _
  (@eq_ap (@Transf K C (@one_cat_native_snake_third_middle_cover_source K C C1 Prod t Add T0 P Q N A B X D b c
  h) B) (@Transf K C (@one_cat_native_snake_third_middle_cover_source K C C1 Prod t Add T0 P Q N A B X D b c h)
  X) (λ v : τ (@Transf K C (@one_cat_native_snake_third_middle_cover_source K C C1 Prod t Add T0 P Q N A B X D b
  c h) B), (@comp_fapp0 (Functor_cat K C) (@one_cat_native_snake_third_middle_cover_source K C C1 Prod t Add T0
  P Q N A B X D b c h) B X b v)) _ _ (@one_cat_native_snake_third_cover_kernel_reconstruction K C C1 Prod t Add
  T0 P Q N A B X D b c h)) (@one_cat_native_snake_third_middle_representative_path K C C1 Prod t Add T0 P Q N A
  B X D b c h))))));

// The original ρ sends that E lift into K(γ).
symbol one_cat_native_snake_third_connecting_representative [K C : Cat]
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
  (@kernel_adjunction_family_func K C (@additive_preadditive C Prod t Add) t (@additive_terminal_object C Prod t
  Add) P (@one_cat_native_snake_gamma_diagram K C (@additive_preadditive C Prod t Add) C1 t
  (@additive_terminal_object C Prod t Add) T0 Q A B X D b c h)))
≔ (@comp_fapp0 (Functor_cat K C) (@one_cat_native_snake_third_middle_cover_source K C C1 Prod t Add T0 P Q N A B
  X D b c h) (@one_cat_native_snake_cover_source K C (@additive_preadditive C Prod t Add) C1 t
  (@additive_terminal_object C Prod t Add) T0 P Q A B X D b c h) (@kernel_adjunction_family_func K C
  (@additive_preadditive C Prod t Add) t (@additive_terminal_object C Prod t Add) P
  (@one_cat_native_snake_gamma_diagram K C (@additive_preadditive C Prod t Add) C1 t (@additive_terminal_object
  C Prod t Add) T0 Q A B X D b c h)) (@one_cat_native_snake_cover_transf K C (@additive_preadditive C Prod t
  Add) C1 t (@additive_terminal_object C Prod t Add) T0 P Q A B X D b c h)
  (@one_cat_native_snake_third_cover_kernel_lift K C C1 Prod t Add T0 P Q N A B X D b c h));

// The original ∂ρ=θ reconstructs ∂z=μrs on both original covers.
symbol one_cat_native_snake_third_connecting_representative_path [K C : Cat]
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
  h) (@cokernel_adjunction_family_func K C (@additive_preadditive C Prod t Add) t T0 Q
  (@one_cat_native_snake_alpha_diagram K C (@additive_preadditive C Prod t Add) C1 t (@additive_terminal_object
  C Prod t Add) T0 P A B X D b c h))) (@comp_fapp0 (Functor_cat K C)
  (@one_cat_native_snake_third_middle_cover_source K C C1 Prod t Add T0 P Q N A B X D b c h)
  (@kernel_adjunction_family_func K C (@additive_preadditive C Prod t Add) t (@additive_terminal_object C Prod t
  Add) P (@one_cat_native_snake_gamma_diagram K C (@additive_preadditive C Prod t Add) C1 t
  (@additive_terminal_object C Prod t Add) T0 Q A B X D b c h)) (@cokernel_adjunction_family_func K C
  (@additive_preadditive C Prod t Add) t T0 Q (@one_cat_native_snake_alpha_diagram K C (@additive_preadditive C
  Prod t Add) C1 t (@additive_terminal_object C Prod t Add) T0 P A B X D b c h))
  (@one_cat_native_snake_connecting_transf K C C1 Prod t Add T0 P Q N A B X D b c h)
  (@one_cat_native_snake_third_connecting_representative K C C1 Prod t Add T0 P Q N A B X D b c h)) (@comp_fapp0
  (Functor_cat K C) (@one_cat_native_snake_third_middle_cover_source K C C1 Prod t Add T0 P Q N A B X D b c h)
  (@kernel_adjunction_family_func K C (@additive_preadditive C Prod t Add) t (@additive_terminal_object C Prod t
  Add) P (@transf_arrow_diagram_func K C (@cokernel_adjunction_family_func K C (@additive_preadditive C Prod t
  Add) t T0 Q (@one_cat_native_snake_alpha_diagram K C (@additive_preadditive C Prod t Add) C1 t
  (@additive_terminal_object C Prod t Add) T0 P A B X D b c h)) (@cokernel_adjunction_family_func K C
  (@additive_preadditive C Prod t Add) t T0 Q (@transf_arrow_diagram_func K C B X b))
  (@one_cat_native_snake_cokernel_first K C (@additive_preadditive C Prod t Add) C1 t (@additive_terminal_object
  C Prod t Add) T0 P Q A B X D b c h))) (@cokernel_adjunction_family_func K C (@additive_preadditive C Prod t
  Add) t T0 Q (@one_cat_native_snake_alpha_diagram K C (@additive_preadditive C Prod t Add) C1 t
  (@additive_terminal_object C Prod t Add) T0 P A B X D b c h)) (@kernel_adjunction_family_inclusion_transf K C
  (@additive_preadditive C Prod t Add) t (@additive_terminal_object C Prod t Add) P (@transf_arrow_diagram_func
  K C (@cokernel_adjunction_family_func K C (@additive_preadditive C Prod t Add) t T0 Q
  (@one_cat_native_snake_alpha_diagram K C (@additive_preadditive C Prod t Add) C1 t (@additive_terminal_object
  C Prod t Add) T0 P A B X D b c h)) (@cokernel_adjunction_family_func K C (@additive_preadditive C Prod t Add)
  t T0 Q (@transf_arrow_diagram_func K C B X b)) (@one_cat_native_snake_cokernel_first K C
  (@additive_preadditive C Prod t Add) C1 t (@additive_terminal_object C Prod t Add) T0 P Q A B X D b c h)))
  (@comp_fapp0 (Functor_cat K C) (@one_cat_native_snake_third_middle_cover_source K C C1 Prod t Add T0 P Q N A B
  X D b c h) (@one_cat_native_snake_third_cover_source K C C1 Prod t Add T0 P Q N A B X D b c h)
  (@kernel_adjunction_family_func K C (@additive_preadditive C Prod t Add) t (@additive_terminal_object C Prod t
  Add) P (@transf_arrow_diagram_func K C (@cokernel_adjunction_family_func K C (@additive_preadditive C Prod t
  Add) t T0 Q (@one_cat_native_snake_alpha_diagram K C (@additive_preadditive C Prod t Add) C1 t
  (@additive_terminal_object C Prod t Add) T0 P A B X D b c h)) (@cokernel_adjunction_family_func K C
  (@additive_preadditive C Prod t Add) t T0 Q (@transf_arrow_diagram_func K C B X b))
  (@one_cat_native_snake_cokernel_first K C (@additive_preadditive C Prod t Add) C1 t (@additive_terminal_object
  C Prod t Add) T0 P Q A B X D b c h))) (@one_cat_native_snake_third_cover_projection K C C1 Prod t Add T0 P Q N
  A B X D b c h) (@one_cat_native_snake_third_middle_cover_first K C C1 Prod t Add T0 P Q N A B X D b c h))))
≔ (@eq_trans _ _ _ _ (@comp_assoc (Functor_cat K C) (@one_cat_native_snake_third_middle_cover_source K C C1 Prod
  t Add T0 P Q N A B X D b c h) (@one_cat_native_snake_cover_source K C (@additive_preadditive C Prod t Add) C1
  t (@additive_terminal_object C Prod t Add) T0 P Q A B X D b c h) (@kernel_adjunction_family_func K C
  (@additive_preadditive C Prod t Add) t (@additive_terminal_object C Prod t Add) P
  (@one_cat_native_snake_gamma_diagram K C (@additive_preadditive C Prod t Add) C1 t (@additive_terminal_object
  C Prod t Add) T0 Q A B X D b c h)) (@cokernel_adjunction_family_func K C (@additive_preadditive C Prod t Add)
  t T0 Q (@one_cat_native_snake_alpha_diagram K C (@additive_preadditive C Prod t Add) C1 t
  (@additive_terminal_object C Prod t Add) T0 P A B X D b c h)) (@one_cat_native_snake_connecting_transf K C C1
  Prod t Add T0 P Q N A B X D b c h) (@one_cat_native_snake_cover_transf K C (@additive_preadditive C Prod t
  Add) C1 t (@additive_terminal_object C Prod t Add) T0 P Q A B X D b c h)
  (@one_cat_native_snake_third_cover_kernel_lift K C C1 Prod t Add T0 P Q N A B X D b c h)) (@eq_trans _ _ _ _
  (@eq_ap (@Transf K C (@one_cat_native_snake_cover_source K C (@additive_preadditive C Prod t Add) C1 t
  (@additive_terminal_object C Prod t Add) T0 P Q A B X D b c h) (@cokernel_adjunction_family_func K C
  (@additive_preadditive C Prod t Add) t T0 Q (@one_cat_native_snake_alpha_diagram K C (@additive_preadditive C
  Prod t Add) C1 t (@additive_terminal_object C Prod t Add) T0 P A B X D b c h))) (@Transf K C
  (@one_cat_native_snake_third_middle_cover_source K C C1 Prod t Add T0 P Q N A B X D b c h)
  (@cokernel_adjunction_family_func K C (@additive_preadditive C Prod t Add) t T0 Q
  (@one_cat_native_snake_alpha_diagram K C (@additive_preadditive C Prod t Add) C1 t (@additive_terminal_object
  C Prod t Add) T0 P A B X D b c h))) (λ v : τ (@Transf K C (@one_cat_native_snake_cover_source K C
  (@additive_preadditive C Prod t Add) C1 t (@additive_terminal_object C Prod t Add) T0 P Q A B X D b c h)
  (@cokernel_adjunction_family_func K C (@additive_preadditive C Prod t Add) t T0 Q
  (@one_cat_native_snake_alpha_diagram K C (@additive_preadditive C Prod t Add) C1 t (@additive_terminal_object
  C Prod t Add) T0 P A B X D b c h))), (@comp_fapp0 (Functor_cat K C)
  (@one_cat_native_snake_third_middle_cover_source K C C1 Prod t Add T0 P Q N A B X D b c h)
  (@one_cat_native_snake_cover_source K C (@additive_preadditive C Prod t Add) C1 t (@additive_terminal_object C
  Prod t Add) T0 P Q A B X D b c h) (@cokernel_adjunction_family_func K C (@additive_preadditive C Prod t Add) t
  T0 Q (@one_cat_native_snake_alpha_diagram K C (@additive_preadditive C Prod t Add) C1 t
  (@additive_terminal_object C Prod t Add) T0 P A B X D b c h)) v (@one_cat_native_snake_third_cover_kernel_lift
  K C C1 Prod t Add T0 P Q N A B X D b c h))) _ _ (@one_cat_native_snake_connecting_reconstruction K C C1 Prod t
  Add T0 P Q N A B X D b c h)) (@eq_trans _ _ _ _ (@eq_sym _ _ _ (@comp_assoc (Functor_cat K C)
  (@one_cat_native_snake_third_middle_cover_source K C C1 Prod t Add T0 P Q N A B X D b c h)
  (@one_cat_native_snake_cover_source K C (@additive_preadditive C Prod t Add) C1 t (@additive_terminal_object C
  Prod t Add) T0 P Q A B X D b c h) (@kernel_adjunction_family_func K C (@additive_preadditive C Prod t Add) t
  (@additive_terminal_object C Prod t Add) P (@transf_arrow_diagram_func K C X D c))
  (@cokernel_adjunction_family_func K C (@additive_preadditive C Prod t Add) t T0 Q
  (@one_cat_native_snake_alpha_diagram K C (@additive_preadditive C Prod t Add) C1 t (@additive_terminal_object
  C Prod t Add) T0 P A B X D b c h)) (@cokernel_adjunction_family_projection_transf K C (@additive_preadditive C
  Prod t Add) t T0 Q (@one_cat_native_snake_alpha_diagram K C (@additive_preadditive C Prod t Add) C1 t
  (@additive_terminal_object C Prod t Add) T0 P A B X D b c h)) (@one_cat_native_snake_covered_lift K C
  (@additive_preadditive C Prod t Add) C1 t (@additive_terminal_object C Prod t Add) T0 P Q A B X D b c h)
  (@one_cat_native_snake_third_cover_kernel_lift K C C1 Prod t Add T0 P Q N A B X D b c h))) (@eq_trans _ _ _ _
  (@eq_ap (@Transf K C (@one_cat_native_snake_third_middle_cover_source K C C1 Prod t Add T0 P Q N A B X D b c
  h) (@kernel_adjunction_family_func K C (@additive_preadditive C Prod t Add) t (@additive_terminal_object C
  Prod t Add) P (@transf_arrow_diagram_func K C X D c))) (@Transf K C
  (@one_cat_native_snake_third_middle_cover_source K C C1 Prod t Add T0 P Q N A B X D b c h)
  (@cokernel_adjunction_family_func K C (@additive_preadditive C Prod t Add) t T0 Q
  (@one_cat_native_snake_alpha_diagram K C (@additive_preadditive C Prod t Add) C1 t (@additive_terminal_object
  C Prod t Add) T0 P A B X D b c h))) (λ v : τ (@Transf K C (@one_cat_native_snake_third_middle_cover_source K C
  C1 Prod t Add T0 P Q N A B X D b c h) (@kernel_adjunction_family_func K C (@additive_preadditive C Prod t Add)
  t (@additive_terminal_object C Prod t Add) P (@transf_arrow_diagram_func K C X D c))), (@comp_fapp0
  (Functor_cat K C) (@one_cat_native_snake_third_middle_cover_source K C C1 Prod t Add T0 P Q N A B X D b c h)
  (@kernel_adjunction_family_func K C (@additive_preadditive C Prod t Add) t (@additive_terminal_object C Prod t
  Add) P (@transf_arrow_diagram_func K C X D c)) (@cokernel_adjunction_family_func K C (@additive_preadditive C
  Prod t Add) t T0 Q (@one_cat_native_snake_alpha_diagram K C (@additive_preadditive C Prod t Add) C1 t
  (@additive_terminal_object C Prod t Add) T0 P A B X D b c h)) (@cokernel_adjunction_family_projection_transf K
  C (@additive_preadditive C Prod t Add) t T0 Q (@one_cat_native_snake_alpha_diagram K C (@additive_preadditive
  C Prod t Add) C1 t (@additive_terminal_object C Prod t Add) T0 P A B X D b c h)) v)) _ _
  (@one_cat_native_snake_third_left_cycle_path K C C1 Prod t Add T0 P Q N A B X D b c h)) (@eq_trans _ _ _ _
  (@comp_assoc (Functor_cat K C) (@one_cat_native_snake_third_middle_cover_source K C C1 Prod t Add T0 P Q N A B
  X D b c h) (@one_cat_native_snake_third_cover_source K C C1 Prod t Add T0 P Q N A B X D b c h)
  (@kernel_adjunction_family_func K C (@additive_preadditive C Prod t Add) t (@additive_terminal_object C Prod t
  Add) P (@transf_arrow_diagram_func K C X D c)) (@cokernel_adjunction_family_func K C (@additive_preadditive C
  Prod t Add) t T0 Q (@one_cat_native_snake_alpha_diagram K C (@additive_preadditive C Prod t Add) C1 t
  (@additive_terminal_object C Prod t Add) T0 P A B X D b c h)) (@cokernel_adjunction_family_projection_transf K
  C (@additive_preadditive C Prod t Add) t T0 Q (@one_cat_native_snake_alpha_diagram K C (@additive_preadditive
  C Prod t Add) C1 t (@additive_terminal_object C Prod t Add) T0 P A B X D b c h))
  (@one_cat_native_snake_third_cover_lift K C C1 Prod t Add T0 P Q N A B X D b c h)
  (@one_cat_native_snake_third_middle_cover_first K C C1 Prod t Add T0 P Q N A B X D b c h)) (@eq_trans _ _ _ _
  (@eq_ap (@Transf K C (@one_cat_native_snake_third_cover_source K C C1 Prod t Add T0 P Q N A B X D b c h)
  (@cokernel_adjunction_family_func K C (@additive_preadditive C Prod t Add) t T0 Q
  (@one_cat_native_snake_alpha_diagram K C (@additive_preadditive C Prod t Add) C1 t (@additive_terminal_object
  C Prod t Add) T0 P A B X D b c h))) (@Transf K C (@one_cat_native_snake_third_middle_cover_source K C C1 Prod
  t Add T0 P Q N A B X D b c h) (@cokernel_adjunction_family_func K C (@additive_preadditive C Prod t Add) t T0
  Q (@one_cat_native_snake_alpha_diagram K C (@additive_preadditive C Prod t Add) C1 t
  (@additive_terminal_object C Prod t Add) T0 P A B X D b c h))) (λ v : τ (@Transf K C
  (@one_cat_native_snake_third_cover_source K C C1 Prod t Add T0 P Q N A B X D b c h)
  (@cokernel_adjunction_family_func K C (@additive_preadditive C Prod t Add) t T0 Q
  (@one_cat_native_snake_alpha_diagram K C (@additive_preadditive C Prod t Add) C1 t (@additive_terminal_object
  C Prod t Add) T0 P A B X D b c h))), (@comp_fapp0 (Functor_cat K C)
  (@one_cat_native_snake_third_middle_cover_source K C C1 Prod t Add T0 P Q N A B X D b c h)
  (@one_cat_native_snake_third_cover_source K C C1 Prod t Add T0 P Q N A B X D b c h)
  (@cokernel_adjunction_family_func K C (@additive_preadditive C Prod t Add) t T0 Q
  (@one_cat_native_snake_alpha_diagram K C (@additive_preadditive C Prod t Add) C1 t (@additive_terminal_object
  C Prod t Add) T0 P A B X D b c h)) v (@one_cat_native_snake_third_middle_cover_first K C C1 Prod t Add T0 P Q
  N A B X D b c h))) _ _ (@eq_sym _ _ _ (@one_cat_native_snake_third_cover_compatibility K C C1 Prod t Add T0 P
  Q N A B X D b c h))) (@eq_sym _ _ _ (@comp_assoc (Functor_cat K C)
  (@one_cat_native_snake_third_middle_cover_source K C C1 Prod t Add T0 P Q N A B X D b c h)
  (@one_cat_native_snake_third_cover_source K C C1 Prod t Add T0 P Q N A B X D b c h)
  (@kernel_adjunction_family_func K C (@additive_preadditive C Prod t Add) t (@additive_terminal_object C Prod t
  Add) P (@transf_arrow_diagram_func K C (@cokernel_adjunction_family_func K C (@additive_preadditive C Prod t
  Add) t T0 Q (@one_cat_native_snake_alpha_diagram K C (@additive_preadditive C Prod t Add) C1 t
  (@additive_terminal_object C Prod t Add) T0 P A B X D b c h)) (@cokernel_adjunction_family_func K C
  (@additive_preadditive C Prod t Add) t T0 Q (@transf_arrow_diagram_func K C B X b))
  (@one_cat_native_snake_cokernel_first K C (@additive_preadditive C Prod t Add) C1 t (@additive_terminal_object
  C Prod t Add) T0 P Q A B X D b c h))) (@cokernel_adjunction_family_func K C (@additive_preadditive C Prod t
  Add) t T0 Q (@one_cat_native_snake_alpha_diagram K C (@additive_preadditive C Prod t Add) C1 t
  (@additive_terminal_object C Prod t Add) T0 P A B X D b c h)) (@kernel_adjunction_family_inclusion_transf K C
  (@additive_preadditive C Prod t Add) t (@additive_terminal_object C Prod t Add) P (@transf_arrow_diagram_func
  K C (@cokernel_adjunction_family_func K C (@additive_preadditive C Prod t Add) t T0 Q
  (@one_cat_native_snake_alpha_diagram K C (@additive_preadditive C Prod t Add) C1 t (@additive_terminal_object
  C Prod t Add) T0 P A B X D b c h)) (@cokernel_adjunction_family_func K C (@additive_preadditive C Prod t Add)
  t T0 Q (@transf_arrow_diagram_func K C B X b)) (@one_cat_native_snake_cokernel_first K C
  (@additive_preadditive C Prod t Add) C1 t (@additive_terminal_object C Prod t Add) T0 P Q A B X D b c h)))
  (@one_cat_native_snake_third_cover_projection K C C1 Prod t Add T0 P Q N A B X D b c h)
  (@one_cat_native_snake_third_middle_cover_first K C C1 Prod t Add T0 P Q N A B X D b c h)))))))));
