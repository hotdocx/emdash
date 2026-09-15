/* Corrected whole representatives for the second canonical snake comparison. */
require open emdash.emdash3_2_one_cat_native_snake_second_covers;
require open emdash.emdash3_2_one_cat_additive_family_units;

// Original image reconstruction identifies ℓes=αx.
symbol one_cat_native_snake_second_alpha_representative_path [K C : Cat]
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
  : τ (@= (@Transf K C (@one_cat_native_snake_second_alpha_cover_source K C C1 Prod t Add T0 P Q N A B X D b c
  h) (@kernel_adjunction_family_func K C (@additive_preadditive C Prod t Add) t (@additive_terminal_object C
  Prod t Add) P (@transf_arrow_diagram_func K C X D c))) (@comp_fapp0 (Functor_cat K C)
  (@one_cat_native_snake_second_alpha_cover_source K C C1 Prod t Add T0 P Q N A B X D b c h)
  (@one_cat_native_snake_cover_source K C (@additive_preadditive C Prod t Add) C1 t (@additive_terminal_object C
  Prod t Add) T0 P Q A B X D b c h) (@kernel_adjunction_family_func K C (@additive_preadditive C Prod t Add) t
  (@additive_terminal_object C Prod t Add) P (@transf_arrow_diagram_func K C X D c))
  (@one_cat_native_snake_covered_lift K C (@additive_preadditive C Prod t Add) C1 t (@additive_terminal_object C
  Prod t Add) T0 P Q A B X D b c h) (@comp_fapp0 (Functor_cat K C)
  (@one_cat_native_snake_second_alpha_cover_source K C C1 Prod t Add T0 P Q N A B X D b c h)
  (@one_cat_native_snake_second_cover_source K C C1 Prod t Add T0 P Q N A B X D b c h)
  (@one_cat_native_snake_cover_source K C (@additive_preadditive C Prod t Add) C1 t (@additive_terminal_object C
  Prod t Add) T0 P Q A B X D b c h) (@one_cat_native_snake_second_cover_lift K C C1 Prod t Add T0 P Q N A B X D
  b c h) (@one_cat_native_snake_second_alpha_cover_first K C C1 Prod t Add T0 P Q N A B X D b c h)))
  (@comp_fapp0 (Functor_cat K C) (@one_cat_native_snake_second_alpha_cover_source K C C1 Prod t Add T0 P Q N A B
  X D b c h) A (@kernel_adjunction_family_func K C (@additive_preadditive C Prod t Add) t
  (@additive_terminal_object C Prod t Add) P (@transf_arrow_diagram_func K C X D c))
  (@one_cat_native_snake_alpha K C (@additive_preadditive C Prod t Add) C1 t (@additive_terminal_object C Prod t
  Add) T0 P A B X D b c h) (@one_cat_native_snake_second_alpha_cover_second K C C1 Prod t Add T0 P Q N A B X D b
  c h)))
≔ (@eq_trans _ _ _ _ (@comp_assoc (Functor_cat K C) (@one_cat_native_snake_second_alpha_cover_source K C C1 Prod
  t Add T0 P Q N A B X D b c h) (@one_cat_native_snake_second_cover_source K C C1 Prod t Add T0 P Q N A B X D b
  c h) (@one_cat_native_snake_cover_source K C (@additive_preadditive C Prod t Add) C1 t
  (@additive_terminal_object C Prod t Add) T0 P Q A B X D b c h) (@kernel_adjunction_family_func K C
  (@additive_preadditive C Prod t Add) t (@additive_terminal_object C Prod t Add) P (@transf_arrow_diagram_func
  K C X D c)) (@one_cat_native_snake_covered_lift K C (@additive_preadditive C Prod t Add) C1 t
  (@additive_terminal_object C Prod t Add) T0 P Q A B X D b c h) (@one_cat_native_snake_second_cover_lift K C C1
  Prod t Add T0 P Q N A B X D b c h) (@one_cat_native_snake_second_alpha_cover_first K C C1 Prod t Add T0 P Q N
  A B X D b c h)) (@eq_trans _ _ _ _ (@eq_ap (@Transf K C (@one_cat_native_snake_second_cover_source K C C1 Prod
  t Add T0 P Q N A B X D b c h) (@kernel_adjunction_family_func K C (@additive_preadditive C Prod t Add) t
  (@additive_terminal_object C Prod t Add) P (@transf_arrow_diagram_func K C X D c))) (@Transf K C
  (@one_cat_native_snake_second_alpha_cover_source K C C1 Prod t Add T0 P Q N A B X D b c h)
  (@kernel_adjunction_family_func K C (@additive_preadditive C Prod t Add) t (@additive_terminal_object C Prod t
  Add) P (@transf_arrow_diagram_func K C X D c))) (λ v : τ (@Transf K C
  (@one_cat_native_snake_second_cover_source K C C1 Prod t Add T0 P Q N A B X D b c h)
  (@kernel_adjunction_family_func K C (@additive_preadditive C Prod t Add) t (@additive_terminal_object C Prod t
  Add) P (@transf_arrow_diagram_func K C X D c))), (@comp_fapp0 (Functor_cat K C)
  (@one_cat_native_snake_second_alpha_cover_source K C C1 Prod t Add T0 P Q N A B X D b c h)
  (@one_cat_native_snake_second_cover_source K C C1 Prod t Add T0 P Q N A B X D b c h)
  (@kernel_adjunction_family_func K C (@additive_preadditive C Prod t Add) t (@additive_terminal_object C Prod t
  Add) P (@transf_arrow_diagram_func K C X D c)) v (@one_cat_native_snake_second_alpha_cover_first K C C1 Prod t
  Add T0 P Q N A B X D b c h))) _ _ (@eq_sym _ _ _ (@one_cat_native_snake_second_cover_image_reconstruction K C
  C1 Prod t Add T0 P Q N A B X D b c h))) (@eq_trans _ _ _ _ (@eq_sym _ _ _ (@comp_assoc (Functor_cat K C)
  (@one_cat_native_snake_second_alpha_cover_source K C C1 Prod t Add T0 P Q N A B X D b c h)
  (@one_cat_native_snake_second_cover_source K C C1 Prod t Add T0 P Q N A B X D b c h) (@comp_cat_fapp0 K
  (Functor_cat WalkingArrow_cat C) C (@adjunction_image_func C (@additive_preadditive C Prod t Add) t
  (@additive_terminal_object C Prod t Add) T0 P Q) (@one_cat_native_snake_alpha_diagram K C
  (@additive_preadditive C Prod t Add) C1 t (@additive_terminal_object C Prod t Add) T0 P A B X D b c h))
  (@kernel_adjunction_family_func K C (@additive_preadditive C Prod t Add) t (@additive_terminal_object C Prod t
  Add) P (@transf_arrow_diagram_func K C X D c)) (@kernel_adjunction_family_inclusion_transf K C
  (@additive_preadditive C Prod t Add) t (@additive_terminal_object C Prod t Add) P (@comp_cat_fapp0 K
  (Functor_cat WalkingArrow_cat C) (Functor_cat WalkingArrow_cat C) (@cokernel_adjunction_arrow_func C
  (@additive_preadditive C Prod t Add) t T0 Q) (@one_cat_native_snake_alpha_diagram K C (@additive_preadditive C
  Prod t Add) C1 t (@additive_terminal_object C Prod t Add) T0 P A B X D b c h)))
  (@one_cat_native_snake_second_cover_image_lift K C C1 Prod t Add T0 P Q N A B X D b c h)
  (@one_cat_native_snake_second_alpha_cover_first K C C1 Prod t Add T0 P Q N A B X D b c h))) (@eq_trans _ _ _ _
  (@eq_ap (@Transf K C (@one_cat_native_snake_second_alpha_cover_source K C C1 Prod t Add T0 P Q N A B X D b c
  h) (@comp_cat_fapp0 K (Functor_cat WalkingArrow_cat C) C (@adjunction_image_func C (@additive_preadditive C
  Prod t Add) t (@additive_terminal_object C Prod t Add) T0 P Q) (@one_cat_native_snake_alpha_diagram K C
  (@additive_preadditive C Prod t Add) C1 t (@additive_terminal_object C Prod t Add) T0 P A B X D b c h)))
  (@Transf K C (@one_cat_native_snake_second_alpha_cover_source K C C1 Prod t Add T0 P Q N A B X D b c h)
  (@kernel_adjunction_family_func K C (@additive_preadditive C Prod t Add) t (@additive_terminal_object C Prod t
  Add) P (@transf_arrow_diagram_func K C X D c))) (λ v : τ (@Transf K C
  (@one_cat_native_snake_second_alpha_cover_source K C C1 Prod t Add T0 P Q N A B X D b c h) (@comp_cat_fapp0 K
  (Functor_cat WalkingArrow_cat C) C (@adjunction_image_func C (@additive_preadditive C Prod t Add) t
  (@additive_terminal_object C Prod t Add) T0 P Q) (@one_cat_native_snake_alpha_diagram K C
  (@additive_preadditive C Prod t Add) C1 t (@additive_terminal_object C Prod t Add) T0 P A B X D b c h))),
  (@comp_fapp0 (Functor_cat K C) (@one_cat_native_snake_second_alpha_cover_source K C C1 Prod t Add T0 P Q N A B
  X D b c h) (@comp_cat_fapp0 K (Functor_cat WalkingArrow_cat C) C (@adjunction_image_func C
  (@additive_preadditive C Prod t Add) t (@additive_terminal_object C Prod t Add) T0 P Q)
  (@one_cat_native_snake_alpha_diagram K C (@additive_preadditive C Prod t Add) C1 t (@additive_terminal_object
  C Prod t Add) T0 P A B X D b c h)) (@kernel_adjunction_family_func K C (@additive_preadditive C Prod t Add) t
  (@additive_terminal_object C Prod t Add) P (@transf_arrow_diagram_func K C X D c))
  (@kernel_adjunction_family_inclusion_transf K C (@additive_preadditive C Prod t Add) t
  (@additive_terminal_object C Prod t Add) P (@comp_cat_fapp0 K (Functor_cat WalkingArrow_cat C) (Functor_cat
  WalkingArrow_cat C) (@cokernel_adjunction_arrow_func C (@additive_preadditive C Prod t Add) t T0 Q)
  (@one_cat_native_snake_alpha_diagram K C (@additive_preadditive C Prod t Add) C1 t (@additive_terminal_object
  C Prod t Add) T0 P A B X D b c h))) v)) _ _ (@one_cat_native_snake_second_alpha_cover_compatibility K C C1
  Prod t Add T0 P Q N A B X D b c h)) (@eq_trans _ _ _ _ (@comp_assoc (Functor_cat K C)
  (@one_cat_native_snake_second_alpha_cover_source K C C1 Prod t Add T0 P Q N A B X D b c h) A (@comp_cat_fapp0
  K (Functor_cat WalkingArrow_cat C) C (@adjunction_image_func C (@additive_preadditive C Prod t Add) t
  (@additive_terminal_object C Prod t Add) T0 P Q) (@one_cat_native_snake_alpha_diagram K C
  (@additive_preadditive C Prod t Add) C1 t (@additive_terminal_object C Prod t Add) T0 P A B X D b c h))
  (@kernel_adjunction_family_func K C (@additive_preadditive C Prod t Add) t (@additive_terminal_object C Prod t
  Add) P (@transf_arrow_diagram_func K C X D c)) (@kernel_adjunction_family_inclusion_transf K C
  (@additive_preadditive C Prod t Add) t (@additive_terminal_object C Prod t Add) P (@comp_cat_fapp0 K
  (Functor_cat WalkingArrow_cat C) (Functor_cat WalkingArrow_cat C) (@cokernel_adjunction_arrow_func C
  (@additive_preadditive C Prod t Add) t T0 Q) (@one_cat_native_snake_alpha_diagram K C (@additive_preadditive C
  Prod t Add) C1 t (@additive_terminal_object C Prod t Add) T0 P A B X D b c h)))
  (@one_cat_image_family_source_transf K C (@additive_preadditive C Prod t Add) C1 t (@additive_terminal_object
  C Prod t Add) T0 P Q (@one_cat_native_snake_alpha_diagram K C (@additive_preadditive C Prod t Add) C1 t
  (@additive_terminal_object C Prod t Add) T0 P A B X D b c h)) (@one_cat_native_snake_second_alpha_cover_second
  K C C1 Prod t Add T0 P Q N A B X D b c h)) (@eq_ap (@Transf K C A (@kernel_adjunction_family_func K C
  (@additive_preadditive C Prod t Add) t (@additive_terminal_object C Prod t Add) P (@transf_arrow_diagram_func
  K C X D c))) (@Transf K C (@one_cat_native_snake_second_alpha_cover_source K C C1 Prod t Add T0 P Q N A B X D
  b c h) (@kernel_adjunction_family_func K C (@additive_preadditive C Prod t Add) t (@additive_terminal_object C
  Prod t Add) P (@transf_arrow_diagram_func K C X D c))) (λ v : τ (@Transf K C A (@kernel_adjunction_family_func
  K C (@additive_preadditive C Prod t Add) t (@additive_terminal_object C Prod t Add) P
  (@transf_arrow_diagram_func K C X D c))), (@comp_fapp0 (Functor_cat K C)
  (@one_cat_native_snake_second_alpha_cover_source K C C1 Prod t Add T0 P Q N A B X D b c h) A
  (@kernel_adjunction_family_func K C (@additive_preadditive C Prod t Add) t (@additive_terminal_object C Prod t
  Add) P (@transf_arrow_diagram_func K C X D c)) v (@one_cat_native_snake_second_alpha_cover_second K C C1 Prod
  t Add T0 P Q N A B X D b c h))) _ _ (@one_cat_image_family_source_factor_path K C (@additive_preadditive C
  Prod t Add) C1 t (@additive_terminal_object C Prod t Add) T0 P Q (@one_cat_native_snake_alpha_diagram K C
  (@additive_preadditive C Prod t Add) C1 t (@additive_terminal_object C Prod t Add) T0 P A B X D b c h))))))));

// The original first cover reconstructs ρes=μrs.
symbol one_cat_native_snake_second_total_cover_path [K C : Cat]
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
  : τ (@= (@Transf K C (@one_cat_native_snake_second_alpha_cover_source K C C1 Prod t Add T0 P Q N A B X D b c
  h) (@kernel_adjunction_family_func K C (@additive_preadditive C Prod t Add) t (@additive_terminal_object C
  Prod t Add) P (@one_cat_native_snake_gamma_diagram K C (@additive_preadditive C Prod t Add) C1 t
  (@additive_terminal_object C Prod t Add) T0 Q A B X D b c h))) (@comp_fapp0 (Functor_cat K C)
  (@one_cat_native_snake_second_alpha_cover_source K C C1 Prod t Add T0 P Q N A B X D b c h)
  (@one_cat_native_snake_cover_source K C (@additive_preadditive C Prod t Add) C1 t (@additive_terminal_object C
  Prod t Add) T0 P Q A B X D b c h) (@kernel_adjunction_family_func K C (@additive_preadditive C Prod t Add) t
  (@additive_terminal_object C Prod t Add) P (@one_cat_native_snake_gamma_diagram K C (@additive_preadditive C
  Prod t Add) C1 t (@additive_terminal_object C Prod t Add) T0 Q A B X D b c h))
  (@one_cat_native_snake_cover_transf K C (@additive_preadditive C Prod t Add) C1 t (@additive_terminal_object C
  Prod t Add) T0 P Q A B X D b c h) (@comp_fapp0 (Functor_cat K C)
  (@one_cat_native_snake_second_alpha_cover_source K C C1 Prod t Add T0 P Q N A B X D b c h)
  (@one_cat_native_snake_second_cover_source K C C1 Prod t Add T0 P Q N A B X D b c h)
  (@one_cat_native_snake_cover_source K C (@additive_preadditive C Prod t Add) C1 t (@additive_terminal_object C
  Prod t Add) T0 P Q A B X D b c h) (@one_cat_native_snake_second_cover_lift K C C1 Prod t Add T0 P Q N A B X D
  b c h) (@one_cat_native_snake_second_alpha_cover_first K C C1 Prod t Add T0 P Q N A B X D b c h)))
  (@comp_fapp0 (Functor_cat K C) (@one_cat_native_snake_second_alpha_cover_source K C C1 Prod t Add T0 P Q N A B
  X D b c h) (@kernel_adjunction_family_func K C (@additive_preadditive C Prod t Add) t
  (@additive_terminal_object C Prod t Add) P (@transf_arrow_diagram_func K C (@kernel_adjunction_family_func K C
  (@additive_preadditive C Prod t Add) t (@additive_terminal_object C Prod t Add) P
  (@one_cat_native_snake_gamma_diagram K C (@additive_preadditive C Prod t Add) C1 t (@additive_terminal_object
  C Prod t Add) T0 Q A B X D b c h)) (@cokernel_adjunction_family_func K C (@additive_preadditive C Prod t Add)
  t T0 Q (@one_cat_native_snake_alpha_diagram K C (@additive_preadditive C Prod t Add) C1 t
  (@additive_terminal_object C Prod t Add) T0 P A B X D b c h)) (@one_cat_native_snake_connecting_transf K C C1
  Prod t Add T0 P Q N A B X D b c h))) (@kernel_adjunction_family_func K C (@additive_preadditive C Prod t Add)
  t (@additive_terminal_object C Prod t Add) P (@one_cat_native_snake_gamma_diagram K C (@additive_preadditive C
  Prod t Add) C1 t (@additive_terminal_object C Prod t Add) T0 Q A B X D b c h))
  (@kernel_adjunction_family_inclusion_transf K C (@additive_preadditive C Prod t Add) t
  (@additive_terminal_object C Prod t Add) P (@transf_arrow_diagram_func K C (@kernel_adjunction_family_func K C
  (@additive_preadditive C Prod t Add) t (@additive_terminal_object C Prod t Add) P
  (@one_cat_native_snake_gamma_diagram K C (@additive_preadditive C Prod t Add) C1 t (@additive_terminal_object
  C Prod t Add) T0 Q A B X D b c h)) (@cokernel_adjunction_family_func K C (@additive_preadditive C Prod t Add)
  t T0 Q (@one_cat_native_snake_alpha_diagram K C (@additive_preadditive C Prod t Add) C1 t
  (@additive_terminal_object C Prod t Add) T0 P A B X D b c h)) (@one_cat_native_snake_connecting_transf K C C1
  Prod t Add T0 P Q N A B X D b c h))) (@comp_fapp0 (Functor_cat K C)
  (@one_cat_native_snake_second_alpha_cover_source K C C1 Prod t Add T0 P Q N A B X D b c h)
  (@one_cat_native_snake_second_cover_source K C C1 Prod t Add T0 P Q N A B X D b c h)
  (@kernel_adjunction_family_func K C (@additive_preadditive C Prod t Add) t (@additive_terminal_object C Prod t
  Add) P (@transf_arrow_diagram_func K C (@kernel_adjunction_family_func K C (@additive_preadditive C Prod t
  Add) t (@additive_terminal_object C Prod t Add) P (@one_cat_native_snake_gamma_diagram K C
  (@additive_preadditive C Prod t Add) C1 t (@additive_terminal_object C Prod t Add) T0 Q A B X D b c h))
  (@cokernel_adjunction_family_func K C (@additive_preadditive C Prod t Add) t T0 Q
  (@one_cat_native_snake_alpha_diagram K C (@additive_preadditive C Prod t Add) C1 t (@additive_terminal_object
  C Prod t Add) T0 P A B X D b c h)) (@one_cat_native_snake_connecting_transf K C C1 Prod t Add T0 P Q N A B X D
  b c h))) (@one_cat_native_snake_second_cover_projection K C C1 Prod t Add T0 P Q N A B X D b c h)
  (@one_cat_native_snake_second_alpha_cover_first K C C1 Prod t Add T0 P Q N A B X D b c h))))
≔ (@eq_trans _ _ _ _ (@comp_assoc (Functor_cat K C) (@one_cat_native_snake_second_alpha_cover_source K C C1 Prod
  t Add T0 P Q N A B X D b c h) (@one_cat_native_snake_second_cover_source K C C1 Prod t Add T0 P Q N A B X D b
  c h) (@one_cat_native_snake_cover_source K C (@additive_preadditive C Prod t Add) C1 t
  (@additive_terminal_object C Prod t Add) T0 P Q A B X D b c h) (@kernel_adjunction_family_func K C
  (@additive_preadditive C Prod t Add) t (@additive_terminal_object C Prod t Add) P
  (@one_cat_native_snake_gamma_diagram K C (@additive_preadditive C Prod t Add) C1 t (@additive_terminal_object
  C Prod t Add) T0 Q A B X D b c h)) (@one_cat_native_snake_cover_transf K C (@additive_preadditive C Prod t
  Add) C1 t (@additive_terminal_object C Prod t Add) T0 P Q A B X D b c h)
  (@one_cat_native_snake_second_cover_lift K C C1 Prod t Add T0 P Q N A B X D b c h)
  (@one_cat_native_snake_second_alpha_cover_first K C C1 Prod t Add T0 P Q N A B X D b c h)) (@eq_trans _ _ _ _
  (@eq_ap (@Transf K C (@one_cat_native_snake_second_cover_source K C C1 Prod t Add T0 P Q N A B X D b c h)
  (@kernel_adjunction_family_func K C (@additive_preadditive C Prod t Add) t (@additive_terminal_object C Prod t
  Add) P (@one_cat_native_snake_gamma_diagram K C (@additive_preadditive C Prod t Add) C1 t
  (@additive_terminal_object C Prod t Add) T0 Q A B X D b c h))) (@Transf K C
  (@one_cat_native_snake_second_alpha_cover_source K C C1 Prod t Add T0 P Q N A B X D b c h)
  (@kernel_adjunction_family_func K C (@additive_preadditive C Prod t Add) t (@additive_terminal_object C Prod t
  Add) P (@one_cat_native_snake_gamma_diagram K C (@additive_preadditive C Prod t Add) C1 t
  (@additive_terminal_object C Prod t Add) T0 Q A B X D b c h))) (λ v : τ (@Transf K C
  (@one_cat_native_snake_second_cover_source K C C1 Prod t Add T0 P Q N A B X D b c h)
  (@kernel_adjunction_family_func K C (@additive_preadditive C Prod t Add) t (@additive_terminal_object C Prod t
  Add) P (@one_cat_native_snake_gamma_diagram K C (@additive_preadditive C Prod t Add) C1 t
  (@additive_terminal_object C Prod t Add) T0 Q A B X D b c h))), (@comp_fapp0 (Functor_cat K C)
  (@one_cat_native_snake_second_alpha_cover_source K C C1 Prod t Add T0 P Q N A B X D b c h)
  (@one_cat_native_snake_second_cover_source K C C1 Prod t Add T0 P Q N A B X D b c h)
  (@kernel_adjunction_family_func K C (@additive_preadditive C Prod t Add) t (@additive_terminal_object C Prod t
  Add) P (@one_cat_native_snake_gamma_diagram K C (@additive_preadditive C Prod t Add) C1 t
  (@additive_terminal_object C Prod t Add) T0 Q A B X D b c h)) v
  (@one_cat_native_snake_second_alpha_cover_first K C C1 Prod t Add T0 P Q N A B X D b c h))) _ _ (@eq_sym _ _ _
  (@one_cat_native_snake_second_cover_compatibility K C C1 Prod t Add T0 P Q N A B X D b c h))) (@eq_sym _ _ _
  (@comp_assoc (Functor_cat K C) (@one_cat_native_snake_second_alpha_cover_source K C C1 Prod t Add T0 P Q N A B
  X D b c h) (@one_cat_native_snake_second_cover_source K C C1 Prod t Add T0 P Q N A B X D b c h)
  (@kernel_adjunction_family_func K C (@additive_preadditive C Prod t Add) t (@additive_terminal_object C Prod t
  Add) P (@transf_arrow_diagram_func K C (@kernel_adjunction_family_func K C (@additive_preadditive C Prod t
  Add) t (@additive_terminal_object C Prod t Add) P (@one_cat_native_snake_gamma_diagram K C
  (@additive_preadditive C Prod t Add) C1 t (@additive_terminal_object C Prod t Add) T0 Q A B X D b c h))
  (@cokernel_adjunction_family_func K C (@additive_preadditive C Prod t Add) t T0 Q
  (@one_cat_native_snake_alpha_diagram K C (@additive_preadditive C Prod t Add) C1 t (@additive_terminal_object
  C Prod t Add) T0 P A B X D b c h)) (@one_cat_native_snake_connecting_transf K C C1 Prod t Add T0 P Q N A B X D
  b c h))) (@kernel_adjunction_family_func K C (@additive_preadditive C Prod t Add) t (@additive_terminal_object
  C Prod t Add) P (@one_cat_native_snake_gamma_diagram K C (@additive_preadditive C Prod t Add) C1 t
  (@additive_terminal_object C Prod t Add) T0 Q A B X D b c h)) (@kernel_adjunction_family_inclusion_transf K C
  (@additive_preadditive C Prod t Add) t (@additive_terminal_object C Prod t Add) P (@transf_arrow_diagram_func
  K C (@kernel_adjunction_family_func K C (@additive_preadditive C Prod t Add) t (@additive_terminal_object C
  Prod t Add) P (@one_cat_native_snake_gamma_diagram K C (@additive_preadditive C Prod t Add) C1 t
  (@additive_terminal_object C Prod t Add) T0 Q A B X D b c h)) (@cokernel_adjunction_family_func K C
  (@additive_preadditive C Prod t Add) t T0 Q (@one_cat_native_snake_alpha_diagram K C (@additive_preadditive C
  Prod t Add) C1 t (@additive_terminal_object C Prod t Add) T0 P A B X D b c h))
  (@one_cat_native_snake_connecting_transf K C C1 Prod t Add T0 P Q N A B X D b c h)))
  (@one_cat_native_snake_second_cover_projection K C C1 Prod t Add T0 P Q N A B X D b c h)
  (@one_cat_native_snake_second_alpha_cover_first K C C1 Prod t Add T0 P Q N A B X D b c h)))));

// The whole difference jes−ax corrects the original E representative.
symbol one_cat_native_snake_second_difference [K C : Cat]
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
  : τ (@Transf K C (@one_cat_native_snake_second_alpha_cover_source K C C1 Prod t Add T0 P Q N A B X D b c h) B)
≔ (@one_cat_difference_family K C C1 Prod t Add T0 (@one_cat_native_snake_second_alpha_cover_source K C C1 Prod
  t Add T0 P Q N A B X D b c h) B (@comp_fapp0 (Functor_cat K C)
  (@one_cat_native_snake_second_alpha_cover_source K C C1 Prod t Add T0 P Q N A B X D b c h)
  (@one_cat_native_snake_cover_source K C (@additive_preadditive C Prod t Add) C1 t (@additive_terminal_object C
  Prod t Add) T0 P Q A B X D b c h) B (@one_cat_native_snake_cover_first K C (@additive_preadditive C Prod t
  Add) C1 t (@additive_terminal_object C Prod t Add) T0 P Q A B X D b c h) (@comp_fapp0 (Functor_cat K C)
  (@one_cat_native_snake_second_alpha_cover_source K C C1 Prod t Add T0 P Q N A B X D b c h)
  (@one_cat_native_snake_second_cover_source K C C1 Prod t Add T0 P Q N A B X D b c h)
  (@one_cat_native_snake_cover_source K C (@additive_preadditive C Prod t Add) C1 t (@additive_terminal_object C
  Prod t Add) T0 P Q A B X D b c h) (@one_cat_native_snake_second_cover_lift K C C1 Prod t Add T0 P Q N A B X D
  b c h) (@one_cat_native_snake_second_alpha_cover_first K C C1 Prod t Add T0 P Q N A B X D b c h)))
  (@comp_fapp0 (Functor_cat K C) (@one_cat_native_snake_second_alpha_cover_source K C C1 Prod t Add T0 P Q N A B
  X D b c h) A B (@native_snake_incoming K C t (@additive_terminal_object C Prod t Add) A B X D b c h)
  (@one_cat_native_snake_second_alpha_cover_second K C C1 Prod t Add T0 P Q N A B X D b c h)));

// Whole bilinearity and original α reconstruction prove b(jes−ax)=0.
symbol one_cat_native_snake_second_difference_zero [K C : Cat]
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
  : τ (@= (@Transf K C (@one_cat_native_snake_second_alpha_cover_source K C C1 Prod t Add T0 P Q N A B X D b c
  h) X) (@comp_fapp0 (Functor_cat K C) (@one_cat_native_snake_second_alpha_cover_source K C C1 Prod t Add T0 P Q
  N A B X D b c h) B X b (@one_cat_native_snake_second_difference K C C1 Prod t Add T0 P Q N A B X D b c h))
  (@zero_arrow_family_zero_transf K C t (@additive_terminal_object C Prod t Add) T0
  (@one_cat_native_snake_second_alpha_cover_source K C C1 Prod t Add T0 P Q N A B X D b c h) X))
≔ (@one_cat_difference_family_postcompose_zero_path K C C1 Prod t Add T0
  (@one_cat_native_snake_second_alpha_cover_source K C C1 Prod t Add T0 P Q N A B X D b c h) B X (@comp_fapp0
  (Functor_cat K C) (@one_cat_native_snake_second_alpha_cover_source K C C1 Prod t Add T0 P Q N A B X D b c h)
  (@one_cat_native_snake_cover_source K C (@additive_preadditive C Prod t Add) C1 t (@additive_terminal_object C
  Prod t Add) T0 P Q A B X D b c h) B (@one_cat_native_snake_cover_first K C (@additive_preadditive C Prod t
  Add) C1 t (@additive_terminal_object C Prod t Add) T0 P Q A B X D b c h) (@comp_fapp0 (Functor_cat K C)
  (@one_cat_native_snake_second_alpha_cover_source K C C1 Prod t Add T0 P Q N A B X D b c h)
  (@one_cat_native_snake_second_cover_source K C C1 Prod t Add T0 P Q N A B X D b c h)
  (@one_cat_native_snake_cover_source K C (@additive_preadditive C Prod t Add) C1 t (@additive_terminal_object C
  Prod t Add) T0 P Q A B X D b c h) (@one_cat_native_snake_second_cover_lift K C C1 Prod t Add T0 P Q N A B X D
  b c h) (@one_cat_native_snake_second_alpha_cover_first K C C1 Prod t Add T0 P Q N A B X D b c h)))
  (@comp_fapp0 (Functor_cat K C) (@one_cat_native_snake_second_alpha_cover_source K C C1 Prod t Add T0 P Q N A B
  X D b c h) A B (@native_snake_incoming K C t (@additive_terminal_object C Prod t Add) A B X D b c h)
  (@one_cat_native_snake_second_alpha_cover_second K C C1 Prod t Add T0 P Q N A B X D b c h)) b (@eq_trans _ _ _
  _ (@comp_assoc (Functor_cat K C) (@one_cat_native_snake_second_alpha_cover_source K C C1 Prod t Add T0 P Q N A
  B X D b c h) (@one_cat_native_snake_cover_source K C (@additive_preadditive C Prod t Add) C1 t
  (@additive_terminal_object C Prod t Add) T0 P Q A B X D b c h) B X b (@one_cat_native_snake_cover_first K C
  (@additive_preadditive C Prod t Add) C1 t (@additive_terminal_object C Prod t Add) T0 P Q A B X D b c h)
  (@comp_fapp0 (Functor_cat K C) (@one_cat_native_snake_second_alpha_cover_source K C C1 Prod t Add T0 P Q N A B
  X D b c h) (@one_cat_native_snake_second_cover_source K C C1 Prod t Add T0 P Q N A B X D b c h)
  (@one_cat_native_snake_cover_source K C (@additive_preadditive C Prod t Add) C1 t (@additive_terminal_object C
  Prod t Add) T0 P Q A B X D b c h) (@one_cat_native_snake_second_cover_lift K C C1 Prod t Add T0 P Q N A B X D
  b c h) (@one_cat_native_snake_second_alpha_cover_first K C C1 Prod t Add T0 P Q N A B X D b c h))) (@eq_trans
  _ _ _ _ (@eq_ap (@Transf K C (@one_cat_native_snake_cover_source K C (@additive_preadditive C Prod t Add) C1 t
  (@additive_terminal_object C Prod t Add) T0 P Q A B X D b c h) X) (@Transf K C
  (@one_cat_native_snake_second_alpha_cover_source K C C1 Prod t Add T0 P Q N A B X D b c h) X) (λ v : τ
  (@Transf K C (@one_cat_native_snake_cover_source K C (@additive_preadditive C Prod t Add) C1 t
  (@additive_terminal_object C Prod t Add) T0 P Q A B X D b c h) X), (@comp_fapp0 (Functor_cat K C)
  (@one_cat_native_snake_second_alpha_cover_source K C C1 Prod t Add T0 P Q N A B X D b c h)
  (@one_cat_native_snake_cover_source K C (@additive_preadditive C Prod t Add) C1 t (@additive_terminal_object C
  Prod t Add) T0 P Q A B X D b c h) X v (@comp_fapp0 (Functor_cat K C)
  (@one_cat_native_snake_second_alpha_cover_source K C C1 Prod t Add T0 P Q N A B X D b c h)
  (@one_cat_native_snake_second_cover_source K C C1 Prod t Add T0 P Q N A B X D b c h)
  (@one_cat_native_snake_cover_source K C (@additive_preadditive C Prod t Add) C1 t (@additive_terminal_object C
  Prod t Add) T0 P Q A B X D b c h) (@one_cat_native_snake_second_cover_lift K C C1 Prod t Add T0 P Q N A B X D
  b c h) (@one_cat_native_snake_second_alpha_cover_first K C C1 Prod t Add T0 P Q N A B X D b c h)))) _ _
  (@eq_sym _ _ _ (@one_cat_native_snake_covered_lift_reconstruction K C (@additive_preadditive C Prod t Add) C1
  t (@additive_terminal_object C Prod t Add) T0 P Q A B X D b c h))) (@eq_trans _ _ _ _ (@eq_sym _ _ _
  (@comp_assoc (Functor_cat K C) (@one_cat_native_snake_second_alpha_cover_source K C C1 Prod t Add T0 P Q N A B
  X D b c h) (@one_cat_native_snake_cover_source K C (@additive_preadditive C Prod t Add) C1 t
  (@additive_terminal_object C Prod t Add) T0 P Q A B X D b c h) (@kernel_adjunction_family_func K C
  (@additive_preadditive C Prod t Add) t (@additive_terminal_object C Prod t Add) P (@transf_arrow_diagram_func
  K C X D c)) X (@kernel_adjunction_family_inclusion_transf K C (@additive_preadditive C Prod t Add) t
  (@additive_terminal_object C Prod t Add) P (@transf_arrow_diagram_func K C X D c))
  (@one_cat_native_snake_covered_lift K C (@additive_preadditive C Prod t Add) C1 t (@additive_terminal_object C
  Prod t Add) T0 P Q A B X D b c h) (@comp_fapp0 (Functor_cat K C)
  (@one_cat_native_snake_second_alpha_cover_source K C C1 Prod t Add T0 P Q N A B X D b c h)
  (@one_cat_native_snake_second_cover_source K C C1 Prod t Add T0 P Q N A B X D b c h)
  (@one_cat_native_snake_cover_source K C (@additive_preadditive C Prod t Add) C1 t (@additive_terminal_object C
  Prod t Add) T0 P Q A B X D b c h) (@one_cat_native_snake_second_cover_lift K C C1 Prod t Add T0 P Q N A B X D
  b c h) (@one_cat_native_snake_second_alpha_cover_first K C C1 Prod t Add T0 P Q N A B X D b c h)))) (@eq_trans
  _ _ _ _ (@eq_ap (@Transf K C (@one_cat_native_snake_second_alpha_cover_source K C C1 Prod t Add T0 P Q N A B X
  D b c h) (@kernel_adjunction_family_func K C (@additive_preadditive C Prod t Add) t (@additive_terminal_object
  C Prod t Add) P (@transf_arrow_diagram_func K C X D c))) (@Transf K C
  (@one_cat_native_snake_second_alpha_cover_source K C C1 Prod t Add T0 P Q N A B X D b c h) X) (λ v : τ
  (@Transf K C (@one_cat_native_snake_second_alpha_cover_source K C C1 Prod t Add T0 P Q N A B X D b c h)
  (@kernel_adjunction_family_func K C (@additive_preadditive C Prod t Add) t (@additive_terminal_object C Prod t
  Add) P (@transf_arrow_diagram_func K C X D c))), (@comp_fapp0 (Functor_cat K C)
  (@one_cat_native_snake_second_alpha_cover_source K C C1 Prod t Add T0 P Q N A B X D b c h)
  (@kernel_adjunction_family_func K C (@additive_preadditive C Prod t Add) t (@additive_terminal_object C Prod t
  Add) P (@transf_arrow_diagram_func K C X D c)) X (@kernel_adjunction_family_inclusion_transf K C
  (@additive_preadditive C Prod t Add) t (@additive_terminal_object C Prod t Add) P (@transf_arrow_diagram_func
  K C X D c)) v)) _ _ (@one_cat_native_snake_second_alpha_representative_path K C C1 Prod t Add T0 P Q N A B X D
  b c h)) (@eq_trans _ _ _ _ (@comp_assoc (Functor_cat K C) (@one_cat_native_snake_second_alpha_cover_source K C
  C1 Prod t Add T0 P Q N A B X D b c h) A (@kernel_adjunction_family_func K C (@additive_preadditive C Prod t
  Add) t (@additive_terminal_object C Prod t Add) P (@transf_arrow_diagram_func K C X D c)) X
  (@kernel_adjunction_family_inclusion_transf K C (@additive_preadditive C Prod t Add) t
  (@additive_terminal_object C Prod t Add) P (@transf_arrow_diagram_func K C X D c))
  (@one_cat_native_snake_alpha K C (@additive_preadditive C Prod t Add) C1 t (@additive_terminal_object C Prod t
  Add) T0 P A B X D b c h) (@one_cat_native_snake_second_alpha_cover_second K C C1 Prod t Add T0 P Q N A B X D b
  c h)) (@eq_trans _ _ _ _ (@eq_ap (@Transf K C A X) (@Transf K C
  (@one_cat_native_snake_second_alpha_cover_source K C C1 Prod t Add T0 P Q N A B X D b c h) X) (λ v : τ
  (@Transf K C A X), (@comp_fapp0 (Functor_cat K C) (@one_cat_native_snake_second_alpha_cover_source K C C1 Prod
  t Add T0 P Q N A B X D b c h) A X v (@one_cat_native_snake_second_alpha_cover_second K C C1 Prod t Add T0 P Q
  N A B X D b c h))) _ _ (@one_cat_native_snake_alpha_reconstruction K C (@additive_preadditive C Prod t Add) C1
  t (@additive_terminal_object C Prod t Add) T0 P A B X D b c h)) (@eq_sym _ _ _ (@comp_assoc (Functor_cat K C)
  (@one_cat_native_snake_second_alpha_cover_source K C C1 Prod t Add T0 P Q N A B X D b c h) A B X b
  (@native_snake_incoming K C t (@additive_terminal_object C Prod t Add) A B X D b c h)
  (@one_cat_native_snake_second_alpha_cover_second K C C1 Prod t Add T0 P Q N A B X D b c h))))))))));

// The original whole K mate lifts the corrected representative into K(b).
symbol one_cat_native_snake_second_middle_kernel_lift [K C : Cat]
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
  : τ (@Transf K C (@one_cat_native_snake_second_alpha_cover_source K C C1 Prod t Add T0 P Q N A B X D b c h)
  (@kernel_adjunction_family_func K C (@additive_preadditive C Prod t Add) t (@additive_terminal_object C Prod t
  Add) P (@transf_arrow_diagram_func K C B X b)))
≔ (@one_cat_kernel_family_lift K C (@additive_preadditive C Prod t Add) C1 t (@additive_terminal_object C Prod t
  Add) T0 P (@one_cat_native_snake_second_alpha_cover_source K C C1 Prod t Add T0 P Q N A B X D b c h)
  (@transf_arrow_diagram_func K C B X b) (@one_cat_native_snake_second_difference K C C1 Prod t Add T0 P Q N A B
  X D b c h) (@one_cat_native_snake_second_difference_zero K C C1 Prod t Add T0 P Q N A B X D b c h));

// The original κ_b reconstructs that same difference.
symbol one_cat_native_snake_second_middle_kernel_reconstruction [K C : Cat]
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
  : τ (@= (@Transf K C (@one_cat_native_snake_second_alpha_cover_source K C C1 Prod t Add T0 P Q N A B X D b c
  h) B) (@comp_fapp0 (Functor_cat K C) (@one_cat_native_snake_second_alpha_cover_source K C C1 Prod t Add T0 P Q
  N A B X D b c h) (@kernel_adjunction_family_func K C (@additive_preadditive C Prod t Add) t
  (@additive_terminal_object C Prod t Add) P (@transf_arrow_diagram_func K C B X b)) B
  (@kernel_adjunction_family_inclusion_transf K C (@additive_preadditive C Prod t Add) t
  (@additive_terminal_object C Prod t Add) P (@transf_arrow_diagram_func K C B X b))
  (@one_cat_native_snake_second_middle_kernel_lift K C C1 Prod t Add T0 P Q N A B X D b c h))
  (@one_cat_native_snake_second_difference K C C1 Prod t Add T0 P Q N A B X D b c h))
≔ (@one_cat_kernel_family_lift_ambient_reconstruction K C (@additive_preadditive C Prod t Add) C1 t
  (@additive_terminal_object C Prod t Add) T0 P (@one_cat_native_snake_second_alpha_cover_source K C C1 Prod t
  Add T0 P Q N A B X D b c h) (@transf_arrow_diagram_func K C B X b) (@one_cat_native_snake_second_difference K
  C C1 Prod t Add T0 P Q N A B X D b c h) (@one_cat_native_snake_second_difference_zero K C C1 Prod t Add T0 P Q
  N A B X D b c h));

// The original π_a kills the correction ax and retains jes.
symbol one_cat_native_snake_second_difference_quotient_path [K C : Cat]
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
  : τ (@= (@Transf K C (@one_cat_native_snake_second_alpha_cover_source K C C1 Prod t Add T0 P Q N A B X D b c
  h) (@cokernel_adjunction_family_func K C (@additive_preadditive C Prod t Add) t T0 Q
  (@native_snake_incoming_diagram K C t (@additive_terminal_object C Prod t Add) A B X D b c h))) (@comp_fapp0
  (Functor_cat K C) (@one_cat_native_snake_second_alpha_cover_source K C C1 Prod t Add T0 P Q N A B X D b c h) B
  (@cokernel_adjunction_family_func K C (@additive_preadditive C Prod t Add) t T0 Q
  (@native_snake_incoming_diagram K C t (@additive_terminal_object C Prod t Add) A B X D b c h))
  (@cokernel_adjunction_family_projection_transf K C (@additive_preadditive C Prod t Add) t T0 Q
  (@native_snake_incoming_diagram K C t (@additive_terminal_object C Prod t Add) A B X D b c h))
  (@one_cat_native_snake_second_difference K C C1 Prod t Add T0 P Q N A B X D b c h)) (@comp_fapp0 (Functor_cat
  K C) (@one_cat_native_snake_second_alpha_cover_source K C C1 Prod t Add T0 P Q N A B X D b c h) B
  (@cokernel_adjunction_family_func K C (@additive_preadditive C Prod t Add) t T0 Q
  (@native_snake_incoming_diagram K C t (@additive_terminal_object C Prod t Add) A B X D b c h))
  (@cokernel_adjunction_family_projection_transf K C (@additive_preadditive C Prod t Add) t T0 Q
  (@native_snake_incoming_diagram K C t (@additive_terminal_object C Prod t Add) A B X D b c h)) (@comp_fapp0
  (Functor_cat K C) (@one_cat_native_snake_second_alpha_cover_source K C C1 Prod t Add T0 P Q N A B X D b c h)
  (@one_cat_native_snake_cover_source K C (@additive_preadditive C Prod t Add) C1 t (@additive_terminal_object C
  Prod t Add) T0 P Q A B X D b c h) B (@one_cat_native_snake_cover_first K C (@additive_preadditive C Prod t
  Add) C1 t (@additive_terminal_object C Prod t Add) T0 P Q A B X D b c h) (@comp_fapp0 (Functor_cat K C)
  (@one_cat_native_snake_second_alpha_cover_source K C C1 Prod t Add T0 P Q N A B X D b c h)
  (@one_cat_native_snake_second_cover_source K C C1 Prod t Add T0 P Q N A B X D b c h)
  (@one_cat_native_snake_cover_source K C (@additive_preadditive C Prod t Add) C1 t (@additive_terminal_object C
  Prod t Add) T0 P Q A B X D b c h) (@one_cat_native_snake_second_cover_lift K C C1 Prod t Add T0 P Q N A B X D
  b c h) (@one_cat_native_snake_second_alpha_cover_first K C C1 Prod t Add T0 P Q N A B X D b c h)))))
≔ (@one_cat_difference_killed_second_path K C C1 Prod t Add T0 (@one_cat_native_snake_second_alpha_cover_source
  K C C1 Prod t Add T0 P Q N A B X D b c h) B (@cokernel_adjunction_family_func K C (@additive_preadditive C
  Prod t Add) t T0 Q (@native_snake_incoming_diagram K C t (@additive_terminal_object C Prod t Add) A B X D b c
  h)) (@comp_fapp0 (Functor_cat K C) (@one_cat_native_snake_second_alpha_cover_source K C C1 Prod t Add T0 P Q N
  A B X D b c h) (@one_cat_native_snake_cover_source K C (@additive_preadditive C Prod t Add) C1 t
  (@additive_terminal_object C Prod t Add) T0 P Q A B X D b c h) B (@one_cat_native_snake_cover_first K C
  (@additive_preadditive C Prod t Add) C1 t (@additive_terminal_object C Prod t Add) T0 P Q A B X D b c h)
  (@comp_fapp0 (Functor_cat K C) (@one_cat_native_snake_second_alpha_cover_source K C C1 Prod t Add T0 P Q N A B
  X D b c h) (@one_cat_native_snake_second_cover_source K C C1 Prod t Add T0 P Q N A B X D b c h)
  (@one_cat_native_snake_cover_source K C (@additive_preadditive C Prod t Add) C1 t (@additive_terminal_object C
  Prod t Add) T0 P Q A B X D b c h) (@one_cat_native_snake_second_cover_lift K C C1 Prod t Add T0 P Q N A B X D
  b c h) (@one_cat_native_snake_second_alpha_cover_first K C C1 Prod t Add T0 P Q N A B X D b c h)))
  (@comp_fapp0 (Functor_cat K C) (@one_cat_native_snake_second_alpha_cover_source K C C1 Prod t Add T0 P Q N A B
  X D b c h) A B (@native_snake_incoming K C t (@additive_terminal_object C Prod t Add) A B X D b c h)
  (@one_cat_native_snake_second_alpha_cover_second K C C1 Prod t Add T0 P Q N A B X D b c h))
  (@cokernel_adjunction_family_projection_transf K C (@additive_preadditive C Prod t Add) t T0 Q
  (@native_snake_incoming_diagram K C t (@additive_terminal_object C Prod t Add) A B X D b c h)) (@eq_trans _ _
  _ _ (@comp_assoc (Functor_cat K C) (@one_cat_native_snake_second_alpha_cover_source K C C1 Prod t Add T0 P Q N
  A B X D b c h) A B (@cokernel_adjunction_family_func K C (@additive_preadditive C Prod t Add) t T0 Q
  (@native_snake_incoming_diagram K C t (@additive_terminal_object C Prod t Add) A B X D b c h))
  (@cokernel_adjunction_family_projection_transf K C (@additive_preadditive C Prod t Add) t T0 Q
  (@native_snake_incoming_diagram K C t (@additive_terminal_object C Prod t Add) A B X D b c h))
  (@native_snake_incoming K C t (@additive_terminal_object C Prod t Add) A B X D b c h)
  (@one_cat_native_snake_second_alpha_cover_second K C C1 Prod t Add T0 P Q N A B X D b c h)) (@eq_trans _ _ _ _
  (@eq_ap (@Transf K C A (@cokernel_adjunction_family_func K C (@additive_preadditive C Prod t Add) t T0 Q
  (@native_snake_incoming_diagram K C t (@additive_terminal_object C Prod t Add) A B X D b c h))) (@Transf K C
  (@one_cat_native_snake_second_alpha_cover_source K C C1 Prod t Add T0 P Q N A B X D b c h)
  (@cokernel_adjunction_family_func K C (@additive_preadditive C Prod t Add) t T0 Q
  (@native_snake_incoming_diagram K C t (@additive_terminal_object C Prod t Add) A B X D b c h))) (λ v : τ
  (@Transf K C A (@cokernel_adjunction_family_func K C (@additive_preadditive C Prod t Add) t T0 Q
  (@native_snake_incoming_diagram K C t (@additive_terminal_object C Prod t Add) A B X D b c h))), (@comp_fapp0
  (Functor_cat K C) (@one_cat_native_snake_second_alpha_cover_source K C C1 Prod t Add T0 P Q N A B X D b c h) A
  (@cokernel_adjunction_family_func K C (@additive_preadditive C Prod t Add) t T0 Q
  (@native_snake_incoming_diagram K C t (@additive_terminal_object C Prod t Add) A B X D b c h)) v
  (@one_cat_native_snake_second_alpha_cover_second K C C1 Prod t Add T0 P Q N A B X D b c h))) _ _
  (@one_cat_cokernel_family_annihilation_path K C (@additive_preadditive C Prod t Add) C1 t
  (@additive_terminal_object C Prod t Add) T0 Q (@native_snake_incoming_diagram K C t (@additive_terminal_object
  C Prod t Add) A B X D b c h))) (@one_cat_zero_family_precompose_path K C C1 t (@additive_terminal_object C
  Prod t Add) T0 (@one_cat_native_snake_second_alpha_cover_source K C C1 Prod t Add T0 P Q N A B X D b c h) A
  (@cokernel_adjunction_family_func K C (@additive_preadditive C Prod t Add) t T0 Q
  (@native_snake_incoming_diagram K C t (@additive_terminal_object C Prod t Add) A B X D b c h))
  (@one_cat_native_snake_second_alpha_cover_second K C C1 Prod t Add T0 P Q N A B X D b c h)))));

// Original kernel cancellation gives k₂w=μrs on the derived representatives.
symbol one_cat_native_snake_second_middle_kernel_image_path [K C : Cat]
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
  : τ (@= (@Transf K C (@one_cat_native_snake_second_alpha_cover_source K C C1 Prod t Add T0 P Q N A B X D b c
  h) (@kernel_adjunction_family_func K C (@additive_preadditive C Prod t Add) t (@additive_terminal_object C
  Prod t Add) P (@one_cat_native_snake_gamma_diagram K C (@additive_preadditive C Prod t Add) C1 t
  (@additive_terminal_object C Prod t Add) T0 Q A B X D b c h))) (@comp_fapp0 (Functor_cat K C)
  (@one_cat_native_snake_second_alpha_cover_source K C C1 Prod t Add T0 P Q N A B X D b c h)
  (@kernel_adjunction_family_func K C (@additive_preadditive C Prod t Add) t (@additive_terminal_object C Prod t
  Add) P (@transf_arrow_diagram_func K C B X b)) (@kernel_adjunction_family_func K C (@additive_preadditive C
  Prod t Add) t (@additive_terminal_object C Prod t Add) P (@one_cat_native_snake_gamma_diagram K C
  (@additive_preadditive C Prod t Add) C1 t (@additive_terminal_object C Prod t Add) T0 Q A B X D b c h))
  (@one_cat_native_snake_kernel_second K C (@additive_preadditive C Prod t Add) C1 t (@additive_terminal_object
  C Prod t Add) T0 P Q A B X D b c h) (@one_cat_native_snake_second_middle_kernel_lift K C C1 Prod t Add T0 P Q
  N A B X D b c h)) (@comp_fapp0 (Functor_cat K C) (@one_cat_native_snake_second_alpha_cover_source K C C1 Prod
  t Add T0 P Q N A B X D b c h) (@kernel_adjunction_family_func K C (@additive_preadditive C Prod t Add) t
  (@additive_terminal_object C Prod t Add) P (@transf_arrow_diagram_func K C (@kernel_adjunction_family_func K C
  (@additive_preadditive C Prod t Add) t (@additive_terminal_object C Prod t Add) P
  (@one_cat_native_snake_gamma_diagram K C (@additive_preadditive C Prod t Add) C1 t (@additive_terminal_object
  C Prod t Add) T0 Q A B X D b c h)) (@cokernel_adjunction_family_func K C (@additive_preadditive C Prod t Add)
  t T0 Q (@one_cat_native_snake_alpha_diagram K C (@additive_preadditive C Prod t Add) C1 t
  (@additive_terminal_object C Prod t Add) T0 P A B X D b c h)) (@one_cat_native_snake_connecting_transf K C C1
  Prod t Add T0 P Q N A B X D b c h))) (@kernel_adjunction_family_func K C (@additive_preadditive C Prod t Add)
  t (@additive_terminal_object C Prod t Add) P (@one_cat_native_snake_gamma_diagram K C (@additive_preadditive C
  Prod t Add) C1 t (@additive_terminal_object C Prod t Add) T0 Q A B X D b c h))
  (@kernel_adjunction_family_inclusion_transf K C (@additive_preadditive C Prod t Add) t
  (@additive_terminal_object C Prod t Add) P (@transf_arrow_diagram_func K C (@kernel_adjunction_family_func K C
  (@additive_preadditive C Prod t Add) t (@additive_terminal_object C Prod t Add) P
  (@one_cat_native_snake_gamma_diagram K C (@additive_preadditive C Prod t Add) C1 t (@additive_terminal_object
  C Prod t Add) T0 Q A B X D b c h)) (@cokernel_adjunction_family_func K C (@additive_preadditive C Prod t Add)
  t T0 Q (@one_cat_native_snake_alpha_diagram K C (@additive_preadditive C Prod t Add) C1 t
  (@additive_terminal_object C Prod t Add) T0 P A B X D b c h)) (@one_cat_native_snake_connecting_transf K C C1
  Prod t Add T0 P Q N A B X D b c h))) (@comp_fapp0 (Functor_cat K C)
  (@one_cat_native_snake_second_alpha_cover_source K C C1 Prod t Add T0 P Q N A B X D b c h)
  (@one_cat_native_snake_second_cover_source K C C1 Prod t Add T0 P Q N A B X D b c h)
  (@kernel_adjunction_family_func K C (@additive_preadditive C Prod t Add) t (@additive_terminal_object C Prod t
  Add) P (@transf_arrow_diagram_func K C (@kernel_adjunction_family_func K C (@additive_preadditive C Prod t
  Add) t (@additive_terminal_object C Prod t Add) P (@one_cat_native_snake_gamma_diagram K C
  (@additive_preadditive C Prod t Add) C1 t (@additive_terminal_object C Prod t Add) T0 Q A B X D b c h))
  (@cokernel_adjunction_family_func K C (@additive_preadditive C Prod t Add) t T0 Q
  (@one_cat_native_snake_alpha_diagram K C (@additive_preadditive C Prod t Add) C1 t (@additive_terminal_object
  C Prod t Add) T0 P A B X D b c h)) (@one_cat_native_snake_connecting_transf K C C1 Prod t Add T0 P Q N A B X D
  b c h))) (@one_cat_native_snake_second_cover_projection K C C1 Prod t Add T0 P Q N A B X D b c h)
  (@one_cat_native_snake_second_alpha_cover_first K C C1 Prod t Add T0 P Q N A B X D b c h))))
≔ (@one_cat_kernel_family_inclusion_reflect_path K C (@additive_preadditive C Prod t Add) C1 t
  (@additive_terminal_object C Prod t Add) T0 P (@one_cat_native_snake_second_alpha_cover_source K C C1 Prod t
  Add T0 P Q N A B X D b c h) (@one_cat_native_snake_gamma_diagram K C (@additive_preadditive C Prod t Add) C1 t
  (@additive_terminal_object C Prod t Add) T0 Q A B X D b c h) (@comp_fapp0 (Functor_cat K C)
  (@one_cat_native_snake_second_alpha_cover_source K C C1 Prod t Add T0 P Q N A B X D b c h)
  (@kernel_adjunction_family_func K C (@additive_preadditive C Prod t Add) t (@additive_terminal_object C Prod t
  Add) P (@transf_arrow_diagram_func K C B X b)) (@kernel_adjunction_family_func K C (@additive_preadditive C
  Prod t Add) t (@additive_terminal_object C Prod t Add) P (@one_cat_native_snake_gamma_diagram K C
  (@additive_preadditive C Prod t Add) C1 t (@additive_terminal_object C Prod t Add) T0 Q A B X D b c h))
  (@one_cat_native_snake_kernel_second K C (@additive_preadditive C Prod t Add) C1 t (@additive_terminal_object
  C Prod t Add) T0 P Q A B X D b c h) (@one_cat_native_snake_second_middle_kernel_lift K C C1 Prod t Add T0 P Q
  N A B X D b c h)) (@comp_fapp0 (Functor_cat K C) (@one_cat_native_snake_second_alpha_cover_source K C C1 Prod
  t Add T0 P Q N A B X D b c h) (@kernel_adjunction_family_func K C (@additive_preadditive C Prod t Add) t
  (@additive_terminal_object C Prod t Add) P (@transf_arrow_diagram_func K C (@kernel_adjunction_family_func K C
  (@additive_preadditive C Prod t Add) t (@additive_terminal_object C Prod t Add) P
  (@one_cat_native_snake_gamma_diagram K C (@additive_preadditive C Prod t Add) C1 t (@additive_terminal_object
  C Prod t Add) T0 Q A B X D b c h)) (@cokernel_adjunction_family_func K C (@additive_preadditive C Prod t Add)
  t T0 Q (@one_cat_native_snake_alpha_diagram K C (@additive_preadditive C Prod t Add) C1 t
  (@additive_terminal_object C Prod t Add) T0 P A B X D b c h)) (@one_cat_native_snake_connecting_transf K C C1
  Prod t Add T0 P Q N A B X D b c h))) (@kernel_adjunction_family_func K C (@additive_preadditive C Prod t Add)
  t (@additive_terminal_object C Prod t Add) P (@one_cat_native_snake_gamma_diagram K C (@additive_preadditive C
  Prod t Add) C1 t (@additive_terminal_object C Prod t Add) T0 Q A B X D b c h))
  (@kernel_adjunction_family_inclusion_transf K C (@additive_preadditive C Prod t Add) t
  (@additive_terminal_object C Prod t Add) P (@transf_arrow_diagram_func K C (@kernel_adjunction_family_func K C
  (@additive_preadditive C Prod t Add) t (@additive_terminal_object C Prod t Add) P
  (@one_cat_native_snake_gamma_diagram K C (@additive_preadditive C Prod t Add) C1 t (@additive_terminal_object
  C Prod t Add) T0 Q A B X D b c h)) (@cokernel_adjunction_family_func K C (@additive_preadditive C Prod t Add)
  t T0 Q (@one_cat_native_snake_alpha_diagram K C (@additive_preadditive C Prod t Add) C1 t
  (@additive_terminal_object C Prod t Add) T0 P A B X D b c h)) (@one_cat_native_snake_connecting_transf K C C1
  Prod t Add T0 P Q N A B X D b c h))) (@comp_fapp0 (Functor_cat K C)
  (@one_cat_native_snake_second_alpha_cover_source K C C1 Prod t Add T0 P Q N A B X D b c h)
  (@one_cat_native_snake_second_cover_source K C C1 Prod t Add T0 P Q N A B X D b c h)
  (@kernel_adjunction_family_func K C (@additive_preadditive C Prod t Add) t (@additive_terminal_object C Prod t
  Add) P (@transf_arrow_diagram_func K C (@kernel_adjunction_family_func K C (@additive_preadditive C Prod t
  Add) t (@additive_terminal_object C Prod t Add) P (@one_cat_native_snake_gamma_diagram K C
  (@additive_preadditive C Prod t Add) C1 t (@additive_terminal_object C Prod t Add) T0 Q A B X D b c h))
  (@cokernel_adjunction_family_func K C (@additive_preadditive C Prod t Add) t T0 Q
  (@one_cat_native_snake_alpha_diagram K C (@additive_preadditive C Prod t Add) C1 t (@additive_terminal_object
  C Prod t Add) T0 P A B X D b c h)) (@one_cat_native_snake_connecting_transf K C C1 Prod t Add T0 P Q N A B X D
  b c h))) (@one_cat_native_snake_second_cover_projection K C C1 Prod t Add T0 P Q N A B X D b c h)
  (@one_cat_native_snake_second_alpha_cover_first K C C1 Prod t Add T0 P Q N A B X D b c h))) (@eq_trans _ _ _ _
  (@comp_assoc (Functor_cat K C) (@one_cat_native_snake_second_alpha_cover_source K C C1 Prod t Add T0 P Q N A B
  X D b c h) (@kernel_adjunction_family_func K C (@additive_preadditive C Prod t Add) t
  (@additive_terminal_object C Prod t Add) P (@transf_arrow_diagram_func K C B X b))
  (@kernel_adjunction_family_func K C (@additive_preadditive C Prod t Add) t (@additive_terminal_object C Prod t
  Add) P (@one_cat_native_snake_gamma_diagram K C (@additive_preadditive C Prod t Add) C1 t
  (@additive_terminal_object C Prod t Add) T0 Q A B X D b c h)) (@cokernel_adjunction_family_func K C
  (@additive_preadditive C Prod t Add) t T0 Q (@native_snake_incoming_diagram K C t (@additive_terminal_object C
  Prod t Add) A B X D b c h)) (@kernel_adjunction_family_inclusion_transf K C (@additive_preadditive C Prod t
  Add) t (@additive_terminal_object C Prod t Add) P (@one_cat_native_snake_gamma_diagram K C
  (@additive_preadditive C Prod t Add) C1 t (@additive_terminal_object C Prod t Add) T0 Q A B X D b c h))
  (@one_cat_native_snake_kernel_second K C (@additive_preadditive C Prod t Add) C1 t (@additive_terminal_object
  C Prod t Add) T0 P Q A B X D b c h) (@one_cat_native_snake_second_middle_kernel_lift K C C1 Prod t Add T0 P Q
  N A B X D b c h)) (@eq_trans _ _ _ _ (@eq_ap (@Transf K C (@kernel_adjunction_family_func K C
  (@additive_preadditive C Prod t Add) t (@additive_terminal_object C Prod t Add) P (@transf_arrow_diagram_func
  K C B X b)) (@cokernel_adjunction_family_func K C (@additive_preadditive C Prod t Add) t T0 Q
  (@native_snake_incoming_diagram K C t (@additive_terminal_object C Prod t Add) A B X D b c h))) (@Transf K C
  (@one_cat_native_snake_second_alpha_cover_source K C C1 Prod t Add T0 P Q N A B X D b c h)
  (@cokernel_adjunction_family_func K C (@additive_preadditive C Prod t Add) t T0 Q
  (@native_snake_incoming_diagram K C t (@additive_terminal_object C Prod t Add) A B X D b c h))) (λ v : τ
  (@Transf K C (@kernel_adjunction_family_func K C (@additive_preadditive C Prod t Add) t
  (@additive_terminal_object C Prod t Add) P (@transf_arrow_diagram_func K C B X b))
  (@cokernel_adjunction_family_func K C (@additive_preadditive C Prod t Add) t T0 Q
  (@native_snake_incoming_diagram K C t (@additive_terminal_object C Prod t Add) A B X D b c h))), (@comp_fapp0
  (Functor_cat K C) (@one_cat_native_snake_second_alpha_cover_source K C C1 Prod t Add T0 P Q N A B X D b c h)
  (@kernel_adjunction_family_func K C (@additive_preadditive C Prod t Add) t (@additive_terminal_object C Prod t
  Add) P (@transf_arrow_diagram_func K C B X b)) (@cokernel_adjunction_family_func K C (@additive_preadditive C
  Prod t Add) t T0 Q (@native_snake_incoming_diagram K C t (@additive_terminal_object C Prod t Add) A B X D b c
  h)) v (@one_cat_native_snake_second_middle_kernel_lift K C C1 Prod t Add T0 P Q N A B X D b c h))) _ _
  (@one_cat_native_snake_kernel_second_reconstruction K C (@additive_preadditive C Prod t Add) C1 t
  (@additive_terminal_object C Prod t Add) T0 P Q A B X D b c h)) (@eq_trans _ _ _ _ (@eq_sym _ _ _ (@comp_assoc
  (Functor_cat K C) (@one_cat_native_snake_second_alpha_cover_source K C C1 Prod t Add T0 P Q N A B X D b c h)
  (@kernel_adjunction_family_func K C (@additive_preadditive C Prod t Add) t (@additive_terminal_object C Prod t
  Add) P (@transf_arrow_diagram_func K C B X b)) B (@cokernel_adjunction_family_func K C (@additive_preadditive
  C Prod t Add) t T0 Q (@native_snake_incoming_diagram K C t (@additive_terminal_object C Prod t Add) A B X D b
  c h)) (@cokernel_adjunction_family_projection_transf K C (@additive_preadditive C Prod t Add) t T0 Q
  (@native_snake_incoming_diagram K C t (@additive_terminal_object C Prod t Add) A B X D b c h))
  (@kernel_adjunction_family_inclusion_transf K C (@additive_preadditive C Prod t Add) t
  (@additive_terminal_object C Prod t Add) P (@transf_arrow_diagram_func K C B X b))
  (@one_cat_native_snake_second_middle_kernel_lift K C C1 Prod t Add T0 P Q N A B X D b c h))) (@eq_trans _ _ _
  _ (@eq_ap (@Transf K C (@one_cat_native_snake_second_alpha_cover_source K C C1 Prod t Add T0 P Q N A B X D b c
  h) B) (@Transf K C (@one_cat_native_snake_second_alpha_cover_source K C C1 Prod t Add T0 P Q N A B X D b c h)
  (@cokernel_adjunction_family_func K C (@additive_preadditive C Prod t Add) t T0 Q
  (@native_snake_incoming_diagram K C t (@additive_terminal_object C Prod t Add) A B X D b c h))) (λ v : τ
  (@Transf K C (@one_cat_native_snake_second_alpha_cover_source K C C1 Prod t Add T0 P Q N A B X D b c h) B),
  (@comp_fapp0 (Functor_cat K C) (@one_cat_native_snake_second_alpha_cover_source K C C1 Prod t Add T0 P Q N A B
  X D b c h) B (@cokernel_adjunction_family_func K C (@additive_preadditive C Prod t Add) t T0 Q
  (@native_snake_incoming_diagram K C t (@additive_terminal_object C Prod t Add) A B X D b c h))
  (@cokernel_adjunction_family_projection_transf K C (@additive_preadditive C Prod t Add) t T0 Q
  (@native_snake_incoming_diagram K C t (@additive_terminal_object C Prod t Add) A B X D b c h)) v)) _ _
  (@one_cat_native_snake_second_middle_kernel_reconstruction K C C1 Prod t Add T0 P Q N A B X D b c h))
  (@eq_trans _ _ _ _ (@one_cat_native_snake_second_difference_quotient_path K C C1 Prod t Add T0 P Q N A B X D b
  c h) (@eq_trans _ _ _ _ (@comp_assoc (Functor_cat K C) (@one_cat_native_snake_second_alpha_cover_source K C C1
  Prod t Add T0 P Q N A B X D b c h) (@one_cat_native_snake_cover_source K C (@additive_preadditive C Prod t
  Add) C1 t (@additive_terminal_object C Prod t Add) T0 P Q A B X D b c h) B (@cokernel_adjunction_family_func K
  C (@additive_preadditive C Prod t Add) t T0 Q (@native_snake_incoming_diagram K C t (@additive_terminal_object
  C Prod t Add) A B X D b c h)) (@cokernel_adjunction_family_projection_transf K C (@additive_preadditive C Prod
  t Add) t T0 Q (@native_snake_incoming_diagram K C t (@additive_terminal_object C Prod t Add) A B X D b c h))
  (@one_cat_native_snake_cover_first K C (@additive_preadditive C Prod t Add) C1 t (@additive_terminal_object C
  Prod t Add) T0 P Q A B X D b c h) (@comp_fapp0 (Functor_cat K C)
  (@one_cat_native_snake_second_alpha_cover_source K C C1 Prod t Add T0 P Q N A B X D b c h)
  (@one_cat_native_snake_second_cover_source K C C1 Prod t Add T0 P Q N A B X D b c h)
  (@one_cat_native_snake_cover_source K C (@additive_preadditive C Prod t Add) C1 t (@additive_terminal_object C
  Prod t Add) T0 P Q A B X D b c h) (@one_cat_native_snake_second_cover_lift K C C1 Prod t Add T0 P Q N A B X D
  b c h) (@one_cat_native_snake_second_alpha_cover_first K C C1 Prod t Add T0 P Q N A B X D b c h))) (@eq_trans
  _ _ _ _ (@eq_ap (@Transf K C (@one_cat_native_snake_cover_source K C (@additive_preadditive C Prod t Add) C1 t
  (@additive_terminal_object C Prod t Add) T0 P Q A B X D b c h) (@cokernel_adjunction_family_func K C
  (@additive_preadditive C Prod t Add) t T0 Q (@native_snake_incoming_diagram K C t (@additive_terminal_object C
  Prod t Add) A B X D b c h))) (@Transf K C (@one_cat_native_snake_second_alpha_cover_source K C C1 Prod t Add
  T0 P Q N A B X D b c h) (@cokernel_adjunction_family_func K C (@additive_preadditive C Prod t Add) t T0 Q
  (@native_snake_incoming_diagram K C t (@additive_terminal_object C Prod t Add) A B X D b c h))) (λ v : τ
  (@Transf K C (@one_cat_native_snake_cover_source K C (@additive_preadditive C Prod t Add) C1 t
  (@additive_terminal_object C Prod t Add) T0 P Q A B X D b c h) (@cokernel_adjunction_family_func K C
  (@additive_preadditive C Prod t Add) t T0 Q (@native_snake_incoming_diagram K C t (@additive_terminal_object C
  Prod t Add) A B X D b c h))), (@comp_fapp0 (Functor_cat K C) (@one_cat_native_snake_second_alpha_cover_source
  K C C1 Prod t Add T0 P Q N A B X D b c h) (@one_cat_native_snake_cover_source K C (@additive_preadditive C
  Prod t Add) C1 t (@additive_terminal_object C Prod t Add) T0 P Q A B X D b c h)
  (@cokernel_adjunction_family_func K C (@additive_preadditive C Prod t Add) t T0 Q
  (@native_snake_incoming_diagram K C t (@additive_terminal_object C Prod t Add) A B X D b c h)) v (@comp_fapp0
  (Functor_cat K C) (@one_cat_native_snake_second_alpha_cover_source K C C1 Prod t Add T0 P Q N A B X D b c h)
  (@one_cat_native_snake_second_cover_source K C C1 Prod t Add T0 P Q N A B X D b c h)
  (@one_cat_native_snake_cover_source K C (@additive_preadditive C Prod t Add) C1 t (@additive_terminal_object C
  Prod t Add) T0 P Q A B X D b c h) (@one_cat_native_snake_second_cover_lift K C C1 Prod t Add T0 P Q N A B X D
  b c h) (@one_cat_native_snake_second_alpha_cover_first K C C1 Prod t Add T0 P Q N A B X D b c h)))) _ _
  (@eq_sym _ _ _ (@one_cat_native_snake_cover_reconstruction K C (@additive_preadditive C Prod t Add) C1 t
  (@additive_terminal_object C Prod t Add) T0 P Q A B X D b c h))) (@eq_trans _ _ _ _ (@eq_sym _ _ _
  (@comp_assoc (Functor_cat K C) (@one_cat_native_snake_second_alpha_cover_source K C C1 Prod t Add T0 P Q N A B
  X D b c h) (@one_cat_native_snake_cover_source K C (@additive_preadditive C Prod t Add) C1 t
  (@additive_terminal_object C Prod t Add) T0 P Q A B X D b c h) (@kernel_adjunction_family_func K C
  (@additive_preadditive C Prod t Add) t (@additive_terminal_object C Prod t Add) P
  (@one_cat_native_snake_gamma_diagram K C (@additive_preadditive C Prod t Add) C1 t (@additive_terminal_object
  C Prod t Add) T0 Q A B X D b c h)) (@cokernel_adjunction_family_func K C (@additive_preadditive C Prod t Add)
  t T0 Q (@native_snake_incoming_diagram K C t (@additive_terminal_object C Prod t Add) A B X D b c h))
  (@kernel_adjunction_family_inclusion_transf K C (@additive_preadditive C Prod t Add) t
  (@additive_terminal_object C Prod t Add) P (@one_cat_native_snake_gamma_diagram K C (@additive_preadditive C
  Prod t Add) C1 t (@additive_terminal_object C Prod t Add) T0 Q A B X D b c h))
  (@one_cat_native_snake_cover_transf K C (@additive_preadditive C Prod t Add) C1 t (@additive_terminal_object C
  Prod t Add) T0 P Q A B X D b c h) (@comp_fapp0 (Functor_cat K C)
  (@one_cat_native_snake_second_alpha_cover_source K C C1 Prod t Add T0 P Q N A B X D b c h)
  (@one_cat_native_snake_second_cover_source K C C1 Prod t Add T0 P Q N A B X D b c h)
  (@one_cat_native_snake_cover_source K C (@additive_preadditive C Prod t Add) C1 t (@additive_terminal_object C
  Prod t Add) T0 P Q A B X D b c h) (@one_cat_native_snake_second_cover_lift K C C1 Prod t Add T0 P Q N A B X D
  b c h) (@one_cat_native_snake_second_alpha_cover_first K C C1 Prod t Add T0 P Q N A B X D b c h)))) (@eq_ap
  (@Transf K C (@one_cat_native_snake_second_alpha_cover_source K C C1 Prod t Add T0 P Q N A B X D b c h)
  (@kernel_adjunction_family_func K C (@additive_preadditive C Prod t Add) t (@additive_terminal_object C Prod t
  Add) P (@one_cat_native_snake_gamma_diagram K C (@additive_preadditive C Prod t Add) C1 t
  (@additive_terminal_object C Prod t Add) T0 Q A B X D b c h))) (@Transf K C
  (@one_cat_native_snake_second_alpha_cover_source K C C1 Prod t Add T0 P Q N A B X D b c h)
  (@cokernel_adjunction_family_func K C (@additive_preadditive C Prod t Add) t T0 Q
  (@native_snake_incoming_diagram K C t (@additive_terminal_object C Prod t Add) A B X D b c h))) (λ v : τ
  (@Transf K C (@one_cat_native_snake_second_alpha_cover_source K C C1 Prod t Add T0 P Q N A B X D b c h)
  (@kernel_adjunction_family_func K C (@additive_preadditive C Prod t Add) t (@additive_terminal_object C Prod t
  Add) P (@one_cat_native_snake_gamma_diagram K C (@additive_preadditive C Prod t Add) C1 t
  (@additive_terminal_object C Prod t Add) T0 Q A B X D b c h))), (@comp_fapp0 (Functor_cat K C)
  (@one_cat_native_snake_second_alpha_cover_source K C C1 Prod t Add T0 P Q N A B X D b c h)
  (@kernel_adjunction_family_func K C (@additive_preadditive C Prod t Add) t (@additive_terminal_object C Prod t
  Add) P (@one_cat_native_snake_gamma_diagram K C (@additive_preadditive C Prod t Add) C1 t
  (@additive_terminal_object C Prod t Add) T0 Q A B X D b c h)) (@cokernel_adjunction_family_func K C
  (@additive_preadditive C Prod t Add) t T0 Q (@native_snake_incoming_diagram K C t (@additive_terminal_object C
  Prod t Add) A B X D b c h)) (@kernel_adjunction_family_inclusion_transf K C (@additive_preadditive C Prod t
  Add) t (@additive_terminal_object C Prod t Add) P (@one_cat_native_snake_gamma_diagram K C
  (@additive_preadditive C Prod t Add) C1 t (@additive_terminal_object C Prod t Add) T0 Q A B X D b c h)) v)) _
  _ (@one_cat_native_snake_second_total_cover_path K C C1 Prod t Add T0 P Q N A B X D b c h)))))))))));
