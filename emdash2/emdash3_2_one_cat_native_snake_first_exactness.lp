/* First interior exactness at K(b), through the actual canonical comparison.
   Both zero projections are derived; no output-exactness premise is supplied. */
require open emdash.emdash3_2_one_cat_native_snake_first_cover;
require open emdash.emdash3_2_one_cat_inverse_from_universal_zeros;

// The actual first comparison after its original image-source map reconstructs k1 under κ_k2.
symbol one_cat_native_snake_first_comparison_source_path [K C : Cat]
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
  : τ (@= (@Transf K C (@kernel_adjunction_family_func K C (@additive_preadditive C Prod t Add) t
    (@additive_terminal_object C Prod t Add) P (@one_cat_native_snake_alpha_diagram K C (@additive_preadditive C
    Prod t Add) C1 t (@additive_terminal_object C Prod t Add) T0 P A B X D b c h))
    (@kernel_adjunction_family_func K C (@additive_preadditive C Prod t Add) t (@additive_terminal_object C Prod
    t Add) P (@transf_arrow_diagram_func K C B X b))) (@comp_fapp0 (Functor_cat K C)
    (@kernel_adjunction_family_func K C (@additive_preadditive C Prod t Add) t (@additive_terminal_object C Prod
    t Add) P (@one_cat_native_snake_alpha_diagram K C (@additive_preadditive C Prod t Add) C1 t
    (@additive_terminal_object C Prod t Add) T0 P A B X D b c h)) (@kernel_adjunction_family_func K C
    (@additive_preadditive C Prod t Add) t (@additive_terminal_object C Prod t Add) P
    (@transf_arrow_diagram_func K C (@kernel_adjunction_family_func K C (@additive_preadditive C Prod t Add) t
    (@additive_terminal_object C Prod t Add) P (@transf_arrow_diagram_func K C B X b))
    (@kernel_adjunction_family_func K C (@additive_preadditive C Prod t Add) t (@additive_terminal_object C Prod
    t Add) P (@one_cat_native_snake_gamma_diagram K C (@additive_preadditive C Prod t Add) C1 t
    (@additive_terminal_object C Prod t Add) T0 Q A B X D b c h)) (@one_cat_native_snake_kernel_second K C
    (@additive_preadditive C Prod t Add) C1 t (@additive_terminal_object C Prod t Add) T0 P Q A B X D b c h)))
    (@kernel_adjunction_family_func K C (@additive_preadditive C Prod t Add) t (@additive_terminal_object C Prod
    t Add) P (@transf_arrow_diagram_func K C B X b)) (@kernel_adjunction_family_inclusion_transf K C
    (@additive_preadditive C Prod t Add) t (@additive_terminal_object C Prod t Add) P
    (@transf_arrow_diagram_func K C (@kernel_adjunction_family_func K C (@additive_preadditive C Prod t Add) t
    (@additive_terminal_object C Prod t Add) P (@transf_arrow_diagram_func K C B X b))
    (@kernel_adjunction_family_func K C (@additive_preadditive C Prod t Add) t (@additive_terminal_object C Prod
    t Add) P (@one_cat_native_snake_gamma_diagram K C (@additive_preadditive C Prod t Add) C1 t
    (@additive_terminal_object C Prod t Add) T0 Q A B X D b c h)) (@one_cat_native_snake_kernel_second K C
    (@additive_preadditive C Prod t Add) C1 t (@additive_terminal_object C Prod t Add) T0 P Q A B X D b c h)))
    (@comp_fapp0 (Functor_cat K C) (@kernel_adjunction_family_func K C (@additive_preadditive C Prod t Add) t
    (@additive_terminal_object C Prod t Add) P (@one_cat_native_snake_alpha_diagram K C (@additive_preadditive C
    Prod t Add) C1 t (@additive_terminal_object C Prod t Add) T0 P A B X D b c h)) (@comp_cat_fapp0 K
    (Functor_cat WalkingArrow_cat C) C (@adjunction_image_func C (@additive_preadditive C Prod t Add) t
    (@additive_terminal_object C Prod t Add) T0 P Q) (@zero_arrow_family_incoming_func K C t
    (@additive_terminal_object C Prod t Add) (@kernel_adjunction_family_func K C (@additive_preadditive C Prod t
    Add) t (@additive_terminal_object C Prod t Add) P (@one_cat_native_snake_alpha_diagram K C
    (@additive_preadditive C Prod t Add) C1 t (@additive_terminal_object C Prod t Add) T0 P A B X D b c h))
    (@transf_arrow_diagram_func K C (@kernel_adjunction_family_func K C (@additive_preadditive C Prod t Add) t
    (@additive_terminal_object C Prod t Add) P (@transf_arrow_diagram_func K C B X b))
    (@kernel_adjunction_family_func K C (@additive_preadditive C Prod t Add) t (@additive_terminal_object C Prod
    t Add) P (@one_cat_native_snake_gamma_diagram K C (@additive_preadditive C Prod t Add) C1 t
    (@additive_terminal_object C Prod t Add) T0 Q A B X D b c h)) (@one_cat_native_snake_kernel_second K C
    (@additive_preadditive C Prod t Add) C1 t (@additive_terminal_object C Prod t Add) T0 P Q A B X D b c h))
    (@one_cat_native_snake_first_exact_input K C C1 Prod t Add T0 P Q N A B X D b c h)))
    (@kernel_adjunction_family_func K C (@additive_preadditive C Prod t Add) t (@additive_terminal_object C Prod
    t Add) P (@transf_arrow_diagram_func K C (@kernel_adjunction_family_func K C (@additive_preadditive C Prod t
    Add) t (@additive_terminal_object C Prod t Add) P (@transf_arrow_diagram_func K C B X b))
    (@kernel_adjunction_family_func K C (@additive_preadditive C Prod t Add) t (@additive_terminal_object C Prod
    t Add) P (@one_cat_native_snake_gamma_diagram K C (@additive_preadditive C Prod t Add) C1 t
    (@additive_terminal_object C Prod t Add) T0 Q A B X D b c h)) (@one_cat_native_snake_kernel_second K C
    (@additive_preadditive C Prod t Add) C1 t (@additive_terminal_object C Prod t Add) T0 P Q A B X D b c h)))
    (@one_cat_native_snake_first_exact_comparison K C C1 Prod t Add T0 P Q N A B X D b c h)
    (@one_cat_image_family_source_transf K C (@additive_preadditive C Prod t Add) C1 t
    (@additive_terminal_object C Prod t Add) T0 P Q (@zero_arrow_family_incoming_func K C t
    (@additive_terminal_object C Prod t Add) (@kernel_adjunction_family_func K C (@additive_preadditive C Prod t
    Add) t (@additive_terminal_object C Prod t Add) P (@one_cat_native_snake_alpha_diagram K C
    (@additive_preadditive C Prod t Add) C1 t (@additive_terminal_object C Prod t Add) T0 P A B X D b c h))
    (@transf_arrow_diagram_func K C (@kernel_adjunction_family_func K C (@additive_preadditive C Prod t Add) t
    (@additive_terminal_object C Prod t Add) P (@transf_arrow_diagram_func K C B X b))
    (@kernel_adjunction_family_func K C (@additive_preadditive C Prod t Add) t (@additive_terminal_object C Prod
    t Add) P (@one_cat_native_snake_gamma_diagram K C (@additive_preadditive C Prod t Add) C1 t
    (@additive_terminal_object C Prod t Add) T0 Q A B X D b c h)) (@one_cat_native_snake_kernel_second K C
    (@additive_preadditive C Prod t Add) C1 t (@additive_terminal_object C Prod t Add) T0 P Q A B X D b c h))
    (@one_cat_native_snake_first_exact_input K C C1 Prod t Add T0 P Q N A B X D b c h)))))
    (@one_cat_native_snake_kernel_first K C (@additive_preadditive C Prod t Add) C1 t (@additive_terminal_object
    C Prod t Add) T0 P Q A B X D b c h))
≔ (@eq_trans _ _ _ _ (@comp_assoc (Functor_cat K C) (@kernel_adjunction_family_func K C (@additive_preadditive C
  Prod t Add) t (@additive_terminal_object C Prod t Add) P (@one_cat_native_snake_alpha_diagram K C
  (@additive_preadditive C Prod t Add) C1 t (@additive_terminal_object C Prod t Add) T0 P A B X D b c h))
  (@comp_cat_fapp0 K (Functor_cat WalkingArrow_cat C) C (@adjunction_image_func C (@additive_preadditive C Prod
  t Add) t (@additive_terminal_object C Prod t Add) T0 P Q) (@zero_arrow_family_incoming_func K C t
  (@additive_terminal_object C Prod t Add) (@kernel_adjunction_family_func K C (@additive_preadditive C Prod t
  Add) t (@additive_terminal_object C Prod t Add) P (@one_cat_native_snake_alpha_diagram K C
  (@additive_preadditive C Prod t Add) C1 t (@additive_terminal_object C Prod t Add) T0 P A B X D b c h))
  (@transf_arrow_diagram_func K C (@kernel_adjunction_family_func K C (@additive_preadditive C Prod t Add) t
  (@additive_terminal_object C Prod t Add) P (@transf_arrow_diagram_func K C B X b))
  (@kernel_adjunction_family_func K C (@additive_preadditive C Prod t Add) t (@additive_terminal_object C Prod t
  Add) P (@one_cat_native_snake_gamma_diagram K C (@additive_preadditive C Prod t Add) C1 t
  (@additive_terminal_object C Prod t Add) T0 Q A B X D b c h)) (@one_cat_native_snake_kernel_second K C
  (@additive_preadditive C Prod t Add) C1 t (@additive_terminal_object C Prod t Add) T0 P Q A B X D b c h))
  (@one_cat_native_snake_first_exact_input K C C1 Prod t Add T0 P Q N A B X D b c h)))
  (@kernel_adjunction_family_func K C (@additive_preadditive C Prod t Add) t (@additive_terminal_object C Prod t
  Add) P (@transf_arrow_diagram_func K C (@kernel_adjunction_family_func K C (@additive_preadditive C Prod t
  Add) t (@additive_terminal_object C Prod t Add) P (@transf_arrow_diagram_func K C B X b))
  (@kernel_adjunction_family_func K C (@additive_preadditive C Prod t Add) t (@additive_terminal_object C Prod t
  Add) P (@one_cat_native_snake_gamma_diagram K C (@additive_preadditive C Prod t Add) C1 t
  (@additive_terminal_object C Prod t Add) T0 Q A B X D b c h)) (@one_cat_native_snake_kernel_second K C
  (@additive_preadditive C Prod t Add) C1 t (@additive_terminal_object C Prod t Add) T0 P Q A B X D b c h)))
  (@kernel_adjunction_family_func K C (@additive_preadditive C Prod t Add) t (@additive_terminal_object C Prod t
  Add) P (@transf_arrow_diagram_func K C B X b)) (@kernel_adjunction_family_inclusion_transf K C
  (@additive_preadditive C Prod t Add) t (@additive_terminal_object C Prod t Add) P (@transf_arrow_diagram_func
  K C (@kernel_adjunction_family_func K C (@additive_preadditive C Prod t Add) t (@additive_terminal_object C
  Prod t Add) P (@transf_arrow_diagram_func K C B X b)) (@kernel_adjunction_family_func K C
  (@additive_preadditive C Prod t Add) t (@additive_terminal_object C Prod t Add) P
  (@one_cat_native_snake_gamma_diagram K C (@additive_preadditive C Prod t Add) C1 t (@additive_terminal_object
  C Prod t Add) T0 Q A B X D b c h)) (@one_cat_native_snake_kernel_second K C (@additive_preadditive C Prod t
  Add) C1 t (@additive_terminal_object C Prod t Add) T0 P Q A B X D b c h)))
  (@one_cat_native_snake_first_exact_comparison K C C1 Prod t Add T0 P Q N A B X D b c h)
  (@one_cat_image_family_source_transf K C (@additive_preadditive C Prod t Add) C1 t (@additive_terminal_object
  C Prod t Add) T0 P Q (@zero_arrow_family_incoming_func K C t (@additive_terminal_object C Prod t Add)
  (@kernel_adjunction_family_func K C (@additive_preadditive C Prod t Add) t (@additive_terminal_object C Prod t
  Add) P (@one_cat_native_snake_alpha_diagram K C (@additive_preadditive C Prod t Add) C1 t
  (@additive_terminal_object C Prod t Add) T0 P A B X D b c h)) (@transf_arrow_diagram_func K C
  (@kernel_adjunction_family_func K C (@additive_preadditive C Prod t Add) t (@additive_terminal_object C Prod t
  Add) P (@transf_arrow_diagram_func K C B X b)) (@kernel_adjunction_family_func K C (@additive_preadditive C
  Prod t Add) t (@additive_terminal_object C Prod t Add) P (@one_cat_native_snake_gamma_diagram K C
  (@additive_preadditive C Prod t Add) C1 t (@additive_terminal_object C Prod t Add) T0 Q A B X D b c h))
  (@one_cat_native_snake_kernel_second K C (@additive_preadditive C Prod t Add) C1 t (@additive_terminal_object
  C Prod t Add) T0 P Q A B X D b c h)) (@one_cat_native_snake_first_exact_input K C C1 Prod t Add T0 P Q N A B X
  D b c h)))) (@eq_trans _ _ _ _ (@eq_ap (@Transf K C (@comp_cat_fapp0 K (Functor_cat WalkingArrow_cat C) C
  (@adjunction_image_func C (@additive_preadditive C Prod t Add) t (@additive_terminal_object C Prod t Add) T0 P
  Q) (@zero_arrow_family_incoming_func K C t (@additive_terminal_object C Prod t Add)
  (@kernel_adjunction_family_func K C (@additive_preadditive C Prod t Add) t (@additive_terminal_object C Prod t
  Add) P (@one_cat_native_snake_alpha_diagram K C (@additive_preadditive C Prod t Add) C1 t
  (@additive_terminal_object C Prod t Add) T0 P A B X D b c h)) (@transf_arrow_diagram_func K C
  (@kernel_adjunction_family_func K C (@additive_preadditive C Prod t Add) t (@additive_terminal_object C Prod t
  Add) P (@transf_arrow_diagram_func K C B X b)) (@kernel_adjunction_family_func K C (@additive_preadditive C
  Prod t Add) t (@additive_terminal_object C Prod t Add) P (@one_cat_native_snake_gamma_diagram K C
  (@additive_preadditive C Prod t Add) C1 t (@additive_terminal_object C Prod t Add) T0 Q A B X D b c h))
  (@one_cat_native_snake_kernel_second K C (@additive_preadditive C Prod t Add) C1 t (@additive_terminal_object
  C Prod t Add) T0 P Q A B X D b c h)) (@one_cat_native_snake_first_exact_input K C C1 Prod t Add T0 P Q N A B X
  D b c h))) (@kernel_adjunction_family_func K C (@additive_preadditive C Prod t Add) t
  (@additive_terminal_object C Prod t Add) P (@transf_arrow_diagram_func K C B X b))) (@Transf K C
  (@kernel_adjunction_family_func K C (@additive_preadditive C Prod t Add) t (@additive_terminal_object C Prod t
  Add) P (@one_cat_native_snake_alpha_diagram K C (@additive_preadditive C Prod t Add) C1 t
  (@additive_terminal_object C Prod t Add) T0 P A B X D b c h)) (@kernel_adjunction_family_func K C
  (@additive_preadditive C Prod t Add) t (@additive_terminal_object C Prod t Add) P (@transf_arrow_diagram_func
  K C B X b))) (λ v : τ (@Transf K C (@comp_cat_fapp0 K (Functor_cat WalkingArrow_cat C) C
  (@adjunction_image_func C (@additive_preadditive C Prod t Add) t (@additive_terminal_object C Prod t Add) T0 P
  Q) (@zero_arrow_family_incoming_func K C t (@additive_terminal_object C Prod t Add)
  (@kernel_adjunction_family_func K C (@additive_preadditive C Prod t Add) t (@additive_terminal_object C Prod t
  Add) P (@one_cat_native_snake_alpha_diagram K C (@additive_preadditive C Prod t Add) C1 t
  (@additive_terminal_object C Prod t Add) T0 P A B X D b c h)) (@transf_arrow_diagram_func K C
  (@kernel_adjunction_family_func K C (@additive_preadditive C Prod t Add) t (@additive_terminal_object C Prod t
  Add) P (@transf_arrow_diagram_func K C B X b)) (@kernel_adjunction_family_func K C (@additive_preadditive C
  Prod t Add) t (@additive_terminal_object C Prod t Add) P (@one_cat_native_snake_gamma_diagram K C
  (@additive_preadditive C Prod t Add) C1 t (@additive_terminal_object C Prod t Add) T0 Q A B X D b c h))
  (@one_cat_native_snake_kernel_second K C (@additive_preadditive C Prod t Add) C1 t (@additive_terminal_object
  C Prod t Add) T0 P Q A B X D b c h)) (@one_cat_native_snake_first_exact_input K C C1 Prod t Add T0 P Q N A B X
  D b c h))) (@kernel_adjunction_family_func K C (@additive_preadditive C Prod t Add) t
  (@additive_terminal_object C Prod t Add) P (@transf_arrow_diagram_func K C B X b))), (@comp_fapp0 (Functor_cat
  K C) (@kernel_adjunction_family_func K C (@additive_preadditive C Prod t Add) t (@additive_terminal_object C
  Prod t Add) P (@one_cat_native_snake_alpha_diagram K C (@additive_preadditive C Prod t Add) C1 t
  (@additive_terminal_object C Prod t Add) T0 P A B X D b c h)) (@comp_cat_fapp0 K (Functor_cat WalkingArrow_cat
  C) C (@adjunction_image_func C (@additive_preadditive C Prod t Add) t (@additive_terminal_object C Prod t Add)
  T0 P Q) (@zero_arrow_family_incoming_func K C t (@additive_terminal_object C Prod t Add)
  (@kernel_adjunction_family_func K C (@additive_preadditive C Prod t Add) t (@additive_terminal_object C Prod t
  Add) P (@one_cat_native_snake_alpha_diagram K C (@additive_preadditive C Prod t Add) C1 t
  (@additive_terminal_object C Prod t Add) T0 P A B X D b c h)) (@transf_arrow_diagram_func K C
  (@kernel_adjunction_family_func K C (@additive_preadditive C Prod t Add) t (@additive_terminal_object C Prod t
  Add) P (@transf_arrow_diagram_func K C B X b)) (@kernel_adjunction_family_func K C (@additive_preadditive C
  Prod t Add) t (@additive_terminal_object C Prod t Add) P (@one_cat_native_snake_gamma_diagram K C
  (@additive_preadditive C Prod t Add) C1 t (@additive_terminal_object C Prod t Add) T0 Q A B X D b c h))
  (@one_cat_native_snake_kernel_second K C (@additive_preadditive C Prod t Add) C1 t (@additive_terminal_object
  C Prod t Add) T0 P Q A B X D b c h)) (@one_cat_native_snake_first_exact_input K C C1 Prod t Add T0 P Q N A B X
  D b c h))) (@kernel_adjunction_family_func K C (@additive_preadditive C Prod t Add) t
  (@additive_terminal_object C Prod t Add) P (@transf_arrow_diagram_func K C B X b)) v
  (@one_cat_image_family_source_transf K C (@additive_preadditive C Prod t Add) C1 t (@additive_terminal_object
  C Prod t Add) T0 P Q (@zero_arrow_family_incoming_func K C t (@additive_terminal_object C Prod t Add)
  (@kernel_adjunction_family_func K C (@additive_preadditive C Prod t Add) t (@additive_terminal_object C Prod t
  Add) P (@one_cat_native_snake_alpha_diagram K C (@additive_preadditive C Prod t Add) C1 t
  (@additive_terminal_object C Prod t Add) T0 P A B X D b c h)) (@transf_arrow_diagram_func K C
  (@kernel_adjunction_family_func K C (@additive_preadditive C Prod t Add) t (@additive_terminal_object C Prod t
  Add) P (@transf_arrow_diagram_func K C B X b)) (@kernel_adjunction_family_func K C (@additive_preadditive C
  Prod t Add) t (@additive_terminal_object C Prod t Add) P (@one_cat_native_snake_gamma_diagram K C
  (@additive_preadditive C Prod t Add) C1 t (@additive_terminal_object C Prod t Add) T0 Q A B X D b c h))
  (@one_cat_native_snake_kernel_second K C (@additive_preadditive C Prod t Add) C1 t (@additive_terminal_object
  C Prod t Add) T0 P Q A B X D b c h)) (@one_cat_native_snake_first_exact_input K C C1 Prod t Add T0 P Q N A B X
  D b c h))))) _ _ (@one_cat_image_kernel_ambient_inclusion_path K C (@additive_preadditive C Prod t Add) C1 t
  (@additive_terminal_object C Prod t Add) T0 P Q (@kernel_adjunction_family_func K C (@additive_preadditive C
  Prod t Add) t (@additive_terminal_object C Prod t Add) P (@one_cat_native_snake_alpha_diagram K C
  (@additive_preadditive C Prod t Add) C1 t (@additive_terminal_object C Prod t Add) T0 P A B X D b c h))
  (@transf_arrow_diagram_func K C (@kernel_adjunction_family_func K C (@additive_preadditive C Prod t Add) t
  (@additive_terminal_object C Prod t Add) P (@transf_arrow_diagram_func K C B X b))
  (@kernel_adjunction_family_func K C (@additive_preadditive C Prod t Add) t (@additive_terminal_object C Prod t
  Add) P (@one_cat_native_snake_gamma_diagram K C (@additive_preadditive C Prod t Add) C1 t
  (@additive_terminal_object C Prod t Add) T0 Q A B X D b c h)) (@one_cat_native_snake_kernel_second K C
  (@additive_preadditive C Prod t Add) C1 t (@additive_terminal_object C Prod t Add) T0 P Q A B X D b c h))
  (@one_cat_native_snake_first_exact_input K C C1 Prod t Add T0 P Q N A B X D b c h) N)) (@eq_trans _ _ _ _
  (@one_cat_image_family_source_factor_path K C (@additive_preadditive C Prod t Add) C1 t
  (@additive_terminal_object C Prod t Add) T0 P Q (@zero_arrow_family_incoming_func K C t
  (@additive_terminal_object C Prod t Add) (@kernel_adjunction_family_func K C (@additive_preadditive C Prod t
  Add) t (@additive_terminal_object C Prod t Add) P (@one_cat_native_snake_alpha_diagram K C
  (@additive_preadditive C Prod t Add) C1 t (@additive_terminal_object C Prod t Add) T0 P A B X D b c h))
  (@transf_arrow_diagram_func K C (@kernel_adjunction_family_func K C (@additive_preadditive C Prod t Add) t
  (@additive_terminal_object C Prod t Add) P (@transf_arrow_diagram_func K C B X b))
  (@kernel_adjunction_family_func K C (@additive_preadditive C Prod t Add) t (@additive_terminal_object C Prod t
  Add) P (@one_cat_native_snake_gamma_diagram K C (@additive_preadditive C Prod t Add) C1 t
  (@additive_terminal_object C Prod t Add) T0 Q A B X D b c h)) (@one_cat_native_snake_kernel_second K C
  (@additive_preadditive C Prod t Add) C1 t (@additive_terminal_object C Prod t Add) T0 P Q A B X D b c h))
  (@one_cat_native_snake_first_exact_input K C C1 Prod t Add T0 P Q N A B X D b c h)))
  (@one_cat_kernel_family_input_source_path K C C1 t (@additive_terminal_object C Prod t Add) T0
  (@kernel_adjunction_family_func K C (@additive_preadditive C Prod t Add) t (@additive_terminal_object C Prod t
  Add) P (@one_cat_native_snake_alpha_diagram K C (@additive_preadditive C Prod t Add) C1 t
  (@additive_terminal_object C Prod t Add) T0 P A B X D b c h)) (@transf_arrow_diagram_func K C
  (@kernel_adjunction_family_func K C (@additive_preadditive C Prod t Add) t (@additive_terminal_object C Prod t
  Add) P (@transf_arrow_diagram_func K C B X b)) (@kernel_adjunction_family_func K C (@additive_preadditive C
  Prod t Add) t (@additive_terminal_object C Prod t Add) P (@one_cat_native_snake_gamma_diagram K C
  (@additive_preadditive C Prod t Add) C1 t (@additive_terminal_object C Prod t Add) T0 Q A B X D b c h))
  (@one_cat_native_snake_kernel_second K C (@additive_preadditive C Prod t Add) C1 t (@additive_terminal_object
  C Prod t Add) T0 P Q A B X D b c h)) (@one_cat_native_snake_kernel_first K C (@additive_preadditive C Prod t
  Add) C1 t (@additive_terminal_object C Prod t Add) T0 P Q A B X D b c h)
  (@one_cat_native_snake_kernel_pair_zero K C (@additive_preadditive C Prod t Add) C1 t
  (@additive_terminal_object C Prod t Add) T0 P Q A B X D b c h)))));

// Both original inclusion reconstructions compare the representative maps in K(b).
symbol one_cat_native_snake_first_cover_middle_path [K C : Cat]
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
  : τ (@= (@Transf K C (@one_cat_native_snake_first_cover_source K C (@additive_preadditive C Prod t Add) C1 t
    (@additive_terminal_object C Prod t Add) T0 P Q A B X D b c h) (@kernel_adjunction_family_func K C
    (@additive_preadditive C Prod t Add) t (@additive_terminal_object C Prod t Add) P
    (@transf_arrow_diagram_func K C B X b))) (@comp_fapp0 (Functor_cat K C)
    (@one_cat_native_snake_first_cover_source K C (@additive_preadditive C Prod t Add) C1 t
    (@additive_terminal_object C Prod t Add) T0 P Q A B X D b c h) (@kernel_adjunction_family_func K C
    (@additive_preadditive C Prod t Add) t (@additive_terminal_object C Prod t Add) P
    (@one_cat_native_snake_alpha_diagram K C (@additive_preadditive C Prod t Add) C1 t
    (@additive_terminal_object C Prod t Add) T0 P A B X D b c h)) (@kernel_adjunction_family_func K C
    (@additive_preadditive C Prod t Add) t (@additive_terminal_object C Prod t Add) P
    (@transf_arrow_diagram_func K C B X b)) (@one_cat_native_snake_kernel_first K C (@additive_preadditive C
    Prod t Add) C1 t (@additive_terminal_object C Prod t Add) T0 P Q A B X D b c h)
    (@one_cat_native_snake_first_cover_to_alpha_kernel K C (@additive_preadditive C Prod t Add) C1 t
    (@additive_terminal_object C Prod t Add) T0 P Q A B X D b c h)) (@comp_fapp0 (Functor_cat K C)
    (@one_cat_native_snake_first_cover_source K C (@additive_preadditive C Prod t Add) C1 t
    (@additive_terminal_object C Prod t Add) T0 P Q A B X D b c h) (@kernel_adjunction_family_func K C
    (@additive_preadditive C Prod t Add) t (@additive_terminal_object C Prod t Add) P
    (@transf_arrow_diagram_func K C (@one_cat_native_snake_image_func K C (@additive_preadditive C Prod t Add)
    C1 t (@additive_terminal_object C Prod t Add) T0 P Q A B X D b c h) (@kernel_adjunction_family_func K C
    (@additive_preadditive C Prod t Add) t (@additive_terminal_object C Prod t Add) P
    (@transf_arrow_diagram_func K C X D c)) (@one_cat_native_snake_image_lift K C (@additive_preadditive C Prod
    t Add) C1 t (@additive_terminal_object C Prod t Add) T0 P Q A B X D b c h))) (@kernel_adjunction_family_func
    K C (@additive_preadditive C Prod t Add) t (@additive_terminal_object C Prod t Add) P
    (@transf_arrow_diagram_func K C B X b)) (@one_cat_native_snake_first_image_kernel_to_middle K C
    (@additive_preadditive C Prod t Add) C1 t (@additive_terminal_object C Prod t Add) T0 P Q A B X D b c h)
    (@one_cat_native_snake_first_cover_transf K C (@additive_preadditive C Prod t Add) C1 t
    (@additive_terminal_object C Prod t Add) T0 P Q A B X D b c h)))
≔ (@one_cat_kernel_family_inclusion_reflect_path K C (@additive_preadditive C Prod t Add) C1 t
  (@additive_terminal_object C Prod t Add) T0 P (@one_cat_native_snake_first_cover_source K C
  (@additive_preadditive C Prod t Add) C1 t (@additive_terminal_object C Prod t Add) T0 P Q A B X D b c h)
  (@transf_arrow_diagram_func K C B X b) (@comp_fapp0 (Functor_cat K C)
  (@one_cat_native_snake_first_cover_source K C (@additive_preadditive C Prod t Add) C1 t
  (@additive_terminal_object C Prod t Add) T0 P Q A B X D b c h) (@kernel_adjunction_family_func K C
  (@additive_preadditive C Prod t Add) t (@additive_terminal_object C Prod t Add) P
  (@one_cat_native_snake_alpha_diagram K C (@additive_preadditive C Prod t Add) C1 t (@additive_terminal_object
  C Prod t Add) T0 P A B X D b c h)) (@kernel_adjunction_family_func K C (@additive_preadditive C Prod t Add) t
  (@additive_terminal_object C Prod t Add) P (@transf_arrow_diagram_func K C B X b))
  (@one_cat_native_snake_kernel_first K C (@additive_preadditive C Prod t Add) C1 t (@additive_terminal_object C
  Prod t Add) T0 P Q A B X D b c h) (@one_cat_native_snake_first_cover_to_alpha_kernel K C
  (@additive_preadditive C Prod t Add) C1 t (@additive_terminal_object C Prod t Add) T0 P Q A B X D b c h))
  (@comp_fapp0 (Functor_cat K C) (@one_cat_native_snake_first_cover_source K C (@additive_preadditive C Prod t
  Add) C1 t (@additive_terminal_object C Prod t Add) T0 P Q A B X D b c h) (@kernel_adjunction_family_func K C
  (@additive_preadditive C Prod t Add) t (@additive_terminal_object C Prod t Add) P (@transf_arrow_diagram_func
  K C (@one_cat_native_snake_image_func K C (@additive_preadditive C Prod t Add) C1 t (@additive_terminal_object
  C Prod t Add) T0 P Q A B X D b c h) (@kernel_adjunction_family_func K C (@additive_preadditive C Prod t Add) t
  (@additive_terminal_object C Prod t Add) P (@transf_arrow_diagram_func K C X D c))
  (@one_cat_native_snake_image_lift K C (@additive_preadditive C Prod t Add) C1 t (@additive_terminal_object C
  Prod t Add) T0 P Q A B X D b c h))) (@kernel_adjunction_family_func K C (@additive_preadditive C Prod t Add) t
  (@additive_terminal_object C Prod t Add) P (@transf_arrow_diagram_func K C B X b))
  (@one_cat_native_snake_first_image_kernel_to_middle K C (@additive_preadditive C Prod t Add) C1 t
  (@additive_terminal_object C Prod t Add) T0 P Q A B X D b c h) (@one_cat_native_snake_first_cover_transf K C
  (@additive_preadditive C Prod t Add) C1 t (@additive_terminal_object C Prod t Add) T0 P Q A B X D b c h))
  (@eq_trans _ _ _ _ (@eq_trans _ _ _ _ (@comp_assoc (Functor_cat K C) (@one_cat_native_snake_first_cover_source
  K C (@additive_preadditive C Prod t Add) C1 t (@additive_terminal_object C Prod t Add) T0 P Q A B X D b c h)
  (@kernel_adjunction_family_func K C (@additive_preadditive C Prod t Add) t (@additive_terminal_object C Prod t
  Add) P (@one_cat_native_snake_alpha_diagram K C (@additive_preadditive C Prod t Add) C1 t
  (@additive_terminal_object C Prod t Add) T0 P A B X D b c h)) (@kernel_adjunction_family_func K C
  (@additive_preadditive C Prod t Add) t (@additive_terminal_object C Prod t Add) P (@transf_arrow_diagram_func
  K C B X b)) B (@kernel_adjunction_family_inclusion_transf K C (@additive_preadditive C Prod t Add) t
  (@additive_terminal_object C Prod t Add) P (@transf_arrow_diagram_func K C B X b))
  (@one_cat_native_snake_kernel_first K C (@additive_preadditive C Prod t Add) C1 t (@additive_terminal_object C
  Prod t Add) T0 P Q A B X D b c h) (@one_cat_native_snake_first_cover_to_alpha_kernel K C
  (@additive_preadditive C Prod t Add) C1 t (@additive_terminal_object C Prod t Add) T0 P Q A B X D b c h))
  (@eq_trans _ _ _ _ (@eq_ap (@Transf K C (@kernel_adjunction_family_func K C (@additive_preadditive C Prod t
  Add) t (@additive_terminal_object C Prod t Add) P (@one_cat_native_snake_alpha_diagram K C
  (@additive_preadditive C Prod t Add) C1 t (@additive_terminal_object C Prod t Add) T0 P A B X D b c h)) B)
  (@Transf K C (@one_cat_native_snake_first_cover_source K C (@additive_preadditive C Prod t Add) C1 t
  (@additive_terminal_object C Prod t Add) T0 P Q A B X D b c h) B) (λ v : τ (@Transf K C
  (@kernel_adjunction_family_func K C (@additive_preadditive C Prod t Add) t (@additive_terminal_object C Prod t
  Add) P (@one_cat_native_snake_alpha_diagram K C (@additive_preadditive C Prod t Add) C1 t
  (@additive_terminal_object C Prod t Add) T0 P A B X D b c h)) B), (@comp_fapp0 (Functor_cat K C)
  (@one_cat_native_snake_first_cover_source K C (@additive_preadditive C Prod t Add) C1 t
  (@additive_terminal_object C Prod t Add) T0 P Q A B X D b c h) (@kernel_adjunction_family_func K C
  (@additive_preadditive C Prod t Add) t (@additive_terminal_object C Prod t Add) P
  (@one_cat_native_snake_alpha_diagram K C (@additive_preadditive C Prod t Add) C1 t (@additive_terminal_object
  C Prod t Add) T0 P A B X D b c h)) B v (@one_cat_native_snake_first_cover_to_alpha_kernel K C
  (@additive_preadditive C Prod t Add) C1 t (@additive_terminal_object C Prod t Add) T0 P Q A B X D b c h))) _ _
  (@one_cat_native_snake_kernel_first_reconstruction K C (@additive_preadditive C Prod t Add) C1 t
  (@additive_terminal_object C Prod t Add) T0 P Q A B X D b c h)) (@eq_trans _ _ _ _ (@eq_sym _ _ _ (@comp_assoc
  (Functor_cat K C) (@one_cat_native_snake_first_cover_source K C (@additive_preadditive C Prod t Add) C1 t
  (@additive_terminal_object C Prod t Add) T0 P Q A B X D b c h) (@kernel_adjunction_family_func K C
  (@additive_preadditive C Prod t Add) t (@additive_terminal_object C Prod t Add) P
  (@one_cat_native_snake_alpha_diagram K C (@additive_preadditive C Prod t Add) C1 t (@additive_terminal_object
  C Prod t Add) T0 P A B X D b c h)) A B (@native_snake_incoming K C t (@additive_terminal_object C Prod t Add)
  A B X D b c h) (@kernel_adjunction_family_inclusion_transf K C (@additive_preadditive C Prod t Add) t
  (@additive_terminal_object C Prod t Add) P (@one_cat_native_snake_alpha_diagram K C (@additive_preadditive C
  Prod t Add) C1 t (@additive_terminal_object C Prod t Add) T0 P A B X D b c h))
  (@one_cat_native_snake_first_cover_to_alpha_kernel K C (@additive_preadditive C Prod t Add) C1 t
  (@additive_terminal_object C Prod t Add) T0 P Q A B X D b c h))) (@eq_ap (@Transf K C
  (@one_cat_native_snake_first_cover_source K C (@additive_preadditive C Prod t Add) C1 t
  (@additive_terminal_object C Prod t Add) T0 P Q A B X D b c h) A) (@Transf K C
  (@one_cat_native_snake_first_cover_source K C (@additive_preadditive C Prod t Add) C1 t
  (@additive_terminal_object C Prod t Add) T0 P Q A B X D b c h) B) (λ v : τ (@Transf K C
  (@one_cat_native_snake_first_cover_source K C (@additive_preadditive C Prod t Add) C1 t
  (@additive_terminal_object C Prod t Add) T0 P Q A B X D b c h) A), (@comp_fapp0 (Functor_cat K C)
  (@one_cat_native_snake_first_cover_source K C (@additive_preadditive C Prod t Add) C1 t
  (@additive_terminal_object C Prod t Add) T0 P Q A B X D b c h) A B (@native_snake_incoming K C t
  (@additive_terminal_object C Prod t Add) A B X D b c h) v)) _ _
  (@one_cat_native_snake_first_cover_alpha_reconstruction K C (@additive_preadditive C Prod t Add) C1 t
  (@additive_terminal_object C Prod t Add) T0 P Q A B X D b c h))))) (@eq_sym _ _ _ (@eq_trans _ _ _ _
  (@comp_assoc (Functor_cat K C) (@one_cat_native_snake_first_cover_source K C (@additive_preadditive C Prod t
  Add) C1 t (@additive_terminal_object C Prod t Add) T0 P Q A B X D b c h) (@kernel_adjunction_family_func K C
  (@additive_preadditive C Prod t Add) t (@additive_terminal_object C Prod t Add) P (@transf_arrow_diagram_func
  K C (@one_cat_native_snake_image_func K C (@additive_preadditive C Prod t Add) C1 t (@additive_terminal_object
  C Prod t Add) T0 P Q A B X D b c h) (@kernel_adjunction_family_func K C (@additive_preadditive C Prod t Add) t
  (@additive_terminal_object C Prod t Add) P (@transf_arrow_diagram_func K C X D c))
  (@one_cat_native_snake_image_lift K C (@additive_preadditive C Prod t Add) C1 t (@additive_terminal_object C
  Prod t Add) T0 P Q A B X D b c h))) (@kernel_adjunction_family_func K C (@additive_preadditive C Prod t Add) t
  (@additive_terminal_object C Prod t Add) P (@transf_arrow_diagram_func K C B X b)) B
  (@kernel_adjunction_family_inclusion_transf K C (@additive_preadditive C Prod t Add) t
  (@additive_terminal_object C Prod t Add) P (@transf_arrow_diagram_func K C B X b))
  (@one_cat_native_snake_first_image_kernel_to_middle K C (@additive_preadditive C Prod t Add) C1 t
  (@additive_terminal_object C Prod t Add) T0 P Q A B X D b c h) (@one_cat_native_snake_first_cover_transf K C
  (@additive_preadditive C Prod t Add) C1 t (@additive_terminal_object C Prod t Add) T0 P Q A B X D b c h))
  (@eq_trans _ _ _ _ (@eq_ap (@Transf K C (@kernel_adjunction_family_func K C (@additive_preadditive C Prod t
  Add) t (@additive_terminal_object C Prod t Add) P (@transf_arrow_diagram_func K C
  (@one_cat_native_snake_image_func K C (@additive_preadditive C Prod t Add) C1 t (@additive_terminal_object C
  Prod t Add) T0 P Q A B X D b c h) (@kernel_adjunction_family_func K C (@additive_preadditive C Prod t Add) t
  (@additive_terminal_object C Prod t Add) P (@transf_arrow_diagram_func K C X D c))
  (@one_cat_native_snake_image_lift K C (@additive_preadditive C Prod t Add) C1 t (@additive_terminal_object C
  Prod t Add) T0 P Q A B X D b c h))) B) (@Transf K C (@one_cat_native_snake_first_cover_source K C
  (@additive_preadditive C Prod t Add) C1 t (@additive_terminal_object C Prod t Add) T0 P Q A B X D b c h) B) (λ
  v : τ (@Transf K C (@kernel_adjunction_family_func K C (@additive_preadditive C Prod t Add) t
  (@additive_terminal_object C Prod t Add) P (@transf_arrow_diagram_func K C (@one_cat_native_snake_image_func K
  C (@additive_preadditive C Prod t Add) C1 t (@additive_terminal_object C Prod t Add) T0 P Q A B X D b c h)
  (@kernel_adjunction_family_func K C (@additive_preadditive C Prod t Add) t (@additive_terminal_object C Prod t
  Add) P (@transf_arrow_diagram_func K C X D c)) (@one_cat_native_snake_image_lift K C (@additive_preadditive C
  Prod t Add) C1 t (@additive_terminal_object C Prod t Add) T0 P Q A B X D b c h))) B), (@comp_fapp0
  (Functor_cat K C) (@one_cat_native_snake_first_cover_source K C (@additive_preadditive C Prod t Add) C1 t
  (@additive_terminal_object C Prod t Add) T0 P Q A B X D b c h) (@kernel_adjunction_family_func K C
  (@additive_preadditive C Prod t Add) t (@additive_terminal_object C Prod t Add) P (@transf_arrow_diagram_func
  K C (@one_cat_native_snake_image_func K C (@additive_preadditive C Prod t Add) C1 t (@additive_terminal_object
  C Prod t Add) T0 P Q A B X D b c h) (@kernel_adjunction_family_func K C (@additive_preadditive C Prod t Add) t
  (@additive_terminal_object C Prod t Add) P (@transf_arrow_diagram_func K C X D c))
  (@one_cat_native_snake_image_lift K C (@additive_preadditive C Prod t Add) C1 t (@additive_terminal_object C
  Prod t Add) T0 P Q A B X D b c h))) B v (@one_cat_native_snake_first_cover_transf K C (@additive_preadditive C
  Prod t Add) C1 t (@additive_terminal_object C Prod t Add) T0 P Q A B X D b c h))) _ _
  (@one_cat_native_snake_first_image_kernel_middle_reconstruction K C (@additive_preadditive C Prod t Add) C1 t
  (@additive_terminal_object C Prod t Add) T0 P Q A B X D b c h)) (@eq_trans _ _ _ _ (@eq_sym _ _ _ (@comp_assoc
  (Functor_cat K C) (@one_cat_native_snake_first_cover_source K C (@additive_preadditive C Prod t Add) C1 t
  (@additive_terminal_object C Prod t Add) T0 P Q A B X D b c h) (@kernel_adjunction_family_func K C
  (@additive_preadditive C Prod t Add) t (@additive_terminal_object C Prod t Add) P (@transf_arrow_diagram_func
  K C (@one_cat_native_snake_image_func K C (@additive_preadditive C Prod t Add) C1 t (@additive_terminal_object
  C Prod t Add) T0 P Q A B X D b c h) (@kernel_adjunction_family_func K C (@additive_preadditive C Prod t Add) t
  (@additive_terminal_object C Prod t Add) P (@transf_arrow_diagram_func K C X D c))
  (@one_cat_native_snake_image_lift K C (@additive_preadditive C Prod t Add) C1 t (@additive_terminal_object C
  Prod t Add) T0 P Q A B X D b c h))) (@one_cat_native_snake_image_func K C (@additive_preadditive C Prod t Add)
  C1 t (@additive_terminal_object C Prod t Add) T0 P Q A B X D b c h) B (@one_cat_native_snake_image_inclusion K
  C (@additive_preadditive C Prod t Add) C1 t (@additive_terminal_object C Prod t Add) T0 P Q A B X D b c h)
  (@kernel_adjunction_family_inclusion_transf K C (@additive_preadditive C Prod t Add) t
  (@additive_terminal_object C Prod t Add) P (@transf_arrow_diagram_func K C (@one_cat_native_snake_image_func K
  C (@additive_preadditive C Prod t Add) C1 t (@additive_terminal_object C Prod t Add) T0 P Q A B X D b c h)
  (@kernel_adjunction_family_func K C (@additive_preadditive C Prod t Add) t (@additive_terminal_object C Prod t
  Add) P (@transf_arrow_diagram_func K C X D c)) (@one_cat_native_snake_image_lift K C (@additive_preadditive C
  Prod t Add) C1 t (@additive_terminal_object C Prod t Add) T0 P Q A B X D b c h)))
  (@one_cat_native_snake_first_cover_transf K C (@additive_preadditive C Prod t Add) C1 t
  (@additive_terminal_object C Prod t Add) T0 P Q A B X D b c h))) (@eq_trans _ _ _ _ (@eq_ap (@Transf K C
  (@one_cat_native_snake_first_cover_source K C (@additive_preadditive C Prod t Add) C1 t
  (@additive_terminal_object C Prod t Add) T0 P Q A B X D b c h) (@one_cat_native_snake_image_func K C
  (@additive_preadditive C Prod t Add) C1 t (@additive_terminal_object C Prod t Add) T0 P Q A B X D b c h))
  (@Transf K C (@one_cat_native_snake_first_cover_source K C (@additive_preadditive C Prod t Add) C1 t
  (@additive_terminal_object C Prod t Add) T0 P Q A B X D b c h) B) (λ v : τ (@Transf K C
  (@one_cat_native_snake_first_cover_source K C (@additive_preadditive C Prod t Add) C1 t
  (@additive_terminal_object C Prod t Add) T0 P Q A B X D b c h) (@one_cat_native_snake_image_func K C
  (@additive_preadditive C Prod t Add) C1 t (@additive_terminal_object C Prod t Add) T0 P Q A B X D b c h)),
  (@comp_fapp0 (Functor_cat K C) (@one_cat_native_snake_first_cover_source K C (@additive_preadditive C Prod t
  Add) C1 t (@additive_terminal_object C Prod t Add) T0 P Q A B X D b c h) (@one_cat_native_snake_image_func K C
  (@additive_preadditive C Prod t Add) C1 t (@additive_terminal_object C Prod t Add) T0 P Q A B X D b c h) B
  (@one_cat_native_snake_image_inclusion K C (@additive_preadditive C Prod t Add) C1 t
  (@additive_terminal_object C Prod t Add) T0 P Q A B X D b c h) v)) _ _
  (@one_cat_native_snake_first_cover_square_path K C (@additive_preadditive C Prod t Add) C1 t
  (@additive_terminal_object C Prod t Add) T0 P Q A B X D b c h)) (@eq_trans _ _ _ _ (@comp_assoc (Functor_cat K
  C) (@one_cat_native_snake_first_cover_source K C (@additive_preadditive C Prod t Add) C1 t
  (@additive_terminal_object C Prod t Add) T0 P Q A B X D b c h) A (@one_cat_native_snake_image_func K C
  (@additive_preadditive C Prod t Add) C1 t (@additive_terminal_object C Prod t Add) T0 P Q A B X D b c h) B
  (@one_cat_native_snake_image_inclusion K C (@additive_preadditive C Prod t Add) C1 t
  (@additive_terminal_object C Prod t Add) T0 P Q A B X D b c h) (@one_cat_native_snake_source_image K C
  (@additive_preadditive C Prod t Add) C1 t (@additive_terminal_object C Prod t Add) T0 P Q A B X D b c h)
  (@one_cat_native_snake_first_cover_first K C (@additive_preadditive C Prod t Add) C1 t
  (@additive_terminal_object C Prod t Add) T0 P Q A B X D b c h)) (@eq_ap (@Transf K C A B) (@Transf K C
  (@one_cat_native_snake_first_cover_source K C (@additive_preadditive C Prod t Add) C1 t
  (@additive_terminal_object C Prod t Add) T0 P Q A B X D b c h) B) (λ v : τ (@Transf K C A B), (@comp_fapp0
  (Functor_cat K C) (@one_cat_native_snake_first_cover_source K C (@additive_preadditive C Prod t Add) C1 t
  (@additive_terminal_object C Prod t Add) T0 P Q A B X D b c h) A B v (@one_cat_native_snake_first_cover_first
  K C (@additive_preadditive C Prod t Add) C1 t (@additive_terminal_object C Prod t Add) T0 P Q A B X D b c h)))
  _ _ (@one_cat_native_snake_image_factor_path K C (@additive_preadditive C Prod t Add) C1 t
  (@additive_terminal_object C Prod t Add) T0 P Q A B X D b c h))))))))));

// The actual first comparison factors the original cover representatives.
symbol one_cat_native_snake_first_comparison_covers_path [K C : Cat]
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
  : τ (@= (@Transf K C (@one_cat_native_snake_first_cover_source K C (@additive_preadditive C Prod t Add) C1 t
    (@additive_terminal_object C Prod t Add) T0 P Q A B X D b c h) (@kernel_adjunction_family_func K C
    (@additive_preadditive C Prod t Add) t (@additive_terminal_object C Prod t Add) P
    (@transf_arrow_diagram_func K C (@kernel_adjunction_family_func K C (@additive_preadditive C Prod t Add) t
    (@additive_terminal_object C Prod t Add) P (@transf_arrow_diagram_func K C B X b))
    (@kernel_adjunction_family_func K C (@additive_preadditive C Prod t Add) t (@additive_terminal_object C Prod
    t Add) P (@one_cat_native_snake_gamma_diagram K C (@additive_preadditive C Prod t Add) C1 t
    (@additive_terminal_object C Prod t Add) T0 Q A B X D b c h)) (@one_cat_native_snake_kernel_second K C
    (@additive_preadditive C Prod t Add) C1 t (@additive_terminal_object C Prod t Add) T0 P Q A B X D b c h))))
    (@comp_fapp0 (Functor_cat K C) (@one_cat_native_snake_first_cover_source K C (@additive_preadditive C Prod t
    Add) C1 t (@additive_terminal_object C Prod t Add) T0 P Q A B X D b c h) (@comp_cat_fapp0 K (Functor_cat
    WalkingArrow_cat C) C (@adjunction_image_func C (@additive_preadditive C Prod t Add) t
    (@additive_terminal_object C Prod t Add) T0 P Q) (@zero_arrow_family_incoming_func K C t
    (@additive_terminal_object C Prod t Add) (@kernel_adjunction_family_func K C (@additive_preadditive C Prod t
    Add) t (@additive_terminal_object C Prod t Add) P (@one_cat_native_snake_alpha_diagram K C
    (@additive_preadditive C Prod t Add) C1 t (@additive_terminal_object C Prod t Add) T0 P A B X D b c h))
    (@transf_arrow_diagram_func K C (@kernel_adjunction_family_func K C (@additive_preadditive C Prod t Add) t
    (@additive_terminal_object C Prod t Add) P (@transf_arrow_diagram_func K C B X b))
    (@kernel_adjunction_family_func K C (@additive_preadditive C Prod t Add) t (@additive_terminal_object C Prod
    t Add) P (@one_cat_native_snake_gamma_diagram K C (@additive_preadditive C Prod t Add) C1 t
    (@additive_terminal_object C Prod t Add) T0 Q A B X D b c h)) (@one_cat_native_snake_kernel_second K C
    (@additive_preadditive C Prod t Add) C1 t (@additive_terminal_object C Prod t Add) T0 P Q A B X D b c h))
    (@one_cat_native_snake_first_exact_input K C C1 Prod t Add T0 P Q N A B X D b c h)))
    (@kernel_adjunction_family_func K C (@additive_preadditive C Prod t Add) t (@additive_terminal_object C Prod
    t Add) P (@transf_arrow_diagram_func K C (@kernel_adjunction_family_func K C (@additive_preadditive C Prod t
    Add) t (@additive_terminal_object C Prod t Add) P (@transf_arrow_diagram_func K C B X b))
    (@kernel_adjunction_family_func K C (@additive_preadditive C Prod t Add) t (@additive_terminal_object C Prod
    t Add) P (@one_cat_native_snake_gamma_diagram K C (@additive_preadditive C Prod t Add) C1 t
    (@additive_terminal_object C Prod t Add) T0 Q A B X D b c h)) (@one_cat_native_snake_kernel_second K C
    (@additive_preadditive C Prod t Add) C1 t (@additive_terminal_object C Prod t Add) T0 P Q A B X D b c h)))
    (@one_cat_native_snake_first_exact_comparison K C C1 Prod t Add T0 P Q N A B X D b c h) (@comp_fapp0
    (Functor_cat K C) (@one_cat_native_snake_first_cover_source K C (@additive_preadditive C Prod t Add) C1 t
    (@additive_terminal_object C Prod t Add) T0 P Q A B X D b c h) (@kernel_adjunction_family_func K C
    (@additive_preadditive C Prod t Add) t (@additive_terminal_object C Prod t Add) P
    (@one_cat_native_snake_alpha_diagram K C (@additive_preadditive C Prod t Add) C1 t
    (@additive_terminal_object C Prod t Add) T0 P A B X D b c h)) (@comp_cat_fapp0 K (Functor_cat
    WalkingArrow_cat C) C (@adjunction_image_func C (@additive_preadditive C Prod t Add) t
    (@additive_terminal_object C Prod t Add) T0 P Q) (@zero_arrow_family_incoming_func K C t
    (@additive_terminal_object C Prod t Add) (@kernel_adjunction_family_func K C (@additive_preadditive C Prod t
    Add) t (@additive_terminal_object C Prod t Add) P (@one_cat_native_snake_alpha_diagram K C
    (@additive_preadditive C Prod t Add) C1 t (@additive_terminal_object C Prod t Add) T0 P A B X D b c h))
    (@transf_arrow_diagram_func K C (@kernel_adjunction_family_func K C (@additive_preadditive C Prod t Add) t
    (@additive_terminal_object C Prod t Add) P (@transf_arrow_diagram_func K C B X b))
    (@kernel_adjunction_family_func K C (@additive_preadditive C Prod t Add) t (@additive_terminal_object C Prod
    t Add) P (@one_cat_native_snake_gamma_diagram K C (@additive_preadditive C Prod t Add) C1 t
    (@additive_terminal_object C Prod t Add) T0 Q A B X D b c h)) (@one_cat_native_snake_kernel_second K C
    (@additive_preadditive C Prod t Add) C1 t (@additive_terminal_object C Prod t Add) T0 P Q A B X D b c h))
    (@one_cat_native_snake_first_exact_input K C C1 Prod t Add T0 P Q N A B X D b c h)))
    (@one_cat_image_family_source_transf K C (@additive_preadditive C Prod t Add) C1 t
    (@additive_terminal_object C Prod t Add) T0 P Q (@zero_arrow_family_incoming_func K C t
    (@additive_terminal_object C Prod t Add) (@kernel_adjunction_family_func K C (@additive_preadditive C Prod t
    Add) t (@additive_terminal_object C Prod t Add) P (@one_cat_native_snake_alpha_diagram K C
    (@additive_preadditive C Prod t Add) C1 t (@additive_terminal_object C Prod t Add) T0 P A B X D b c h))
    (@transf_arrow_diagram_func K C (@kernel_adjunction_family_func K C (@additive_preadditive C Prod t Add) t
    (@additive_terminal_object C Prod t Add) P (@transf_arrow_diagram_func K C B X b))
    (@kernel_adjunction_family_func K C (@additive_preadditive C Prod t Add) t (@additive_terminal_object C Prod
    t Add) P (@one_cat_native_snake_gamma_diagram K C (@additive_preadditive C Prod t Add) C1 t
    (@additive_terminal_object C Prod t Add) T0 Q A B X D b c h)) (@one_cat_native_snake_kernel_second K C
    (@additive_preadditive C Prod t Add) C1 t (@additive_terminal_object C Prod t Add) T0 P Q A B X D b c h))
    (@one_cat_native_snake_first_exact_input K C C1 Prod t Add T0 P Q N A B X D b c h)))
    (@one_cat_native_snake_first_cover_to_alpha_kernel K C (@additive_preadditive C Prod t Add) C1 t
    (@additive_terminal_object C Prod t Add) T0 P Q A B X D b c h))) (@comp_fapp0 (Functor_cat K C)
    (@one_cat_native_snake_first_cover_source K C (@additive_preadditive C Prod t Add) C1 t
    (@additive_terminal_object C Prod t Add) T0 P Q A B X D b c h) (@kernel_adjunction_family_func K C
    (@additive_preadditive C Prod t Add) t (@additive_terminal_object C Prod t Add) P
    (@transf_arrow_diagram_func K C (@one_cat_native_snake_image_func K C (@additive_preadditive C Prod t Add)
    C1 t (@additive_terminal_object C Prod t Add) T0 P Q A B X D b c h) (@kernel_adjunction_family_func K C
    (@additive_preadditive C Prod t Add) t (@additive_terminal_object C Prod t Add) P
    (@transf_arrow_diagram_func K C X D c)) (@one_cat_native_snake_image_lift K C (@additive_preadditive C Prod
    t Add) C1 t (@additive_terminal_object C Prod t Add) T0 P Q A B X D b c h))) (@kernel_adjunction_family_func
    K C (@additive_preadditive C Prod t Add) t (@additive_terminal_object C Prod t Add) P
    (@transf_arrow_diagram_func K C (@kernel_adjunction_family_func K C (@additive_preadditive C Prod t Add) t
    (@additive_terminal_object C Prod t Add) P (@transf_arrow_diagram_func K C B X b))
    (@kernel_adjunction_family_func K C (@additive_preadditive C Prod t Add) t (@additive_terminal_object C Prod
    t Add) P (@one_cat_native_snake_gamma_diagram K C (@additive_preadditive C Prod t Add) C1 t
    (@additive_terminal_object C Prod t Add) T0 Q A B X D b c h)) (@one_cat_native_snake_kernel_second K C
    (@additive_preadditive C Prod t Add) C1 t (@additive_terminal_object C Prod t Add) T0 P Q A B X D b c h)))
    (@one_cat_native_snake_first_image_kernel_to_kernel K C (@additive_preadditive C Prod t Add) C1 t
    (@additive_terminal_object C Prod t Add) T0 P Q A B X D b c h) (@one_cat_native_snake_first_cover_transf K C
    (@additive_preadditive C Prod t Add) C1 t (@additive_terminal_object C Prod t Add) T0 P Q A B X D b c h)))
≔ (@one_cat_kernel_family_inclusion_reflect_path K C (@additive_preadditive C Prod t Add) C1 t
  (@additive_terminal_object C Prod t Add) T0 P (@one_cat_native_snake_first_cover_source K C
  (@additive_preadditive C Prod t Add) C1 t (@additive_terminal_object C Prod t Add) T0 P Q A B X D b c h)
  (@transf_arrow_diagram_func K C (@kernel_adjunction_family_func K C (@additive_preadditive C Prod t Add) t
  (@additive_terminal_object C Prod t Add) P (@transf_arrow_diagram_func K C B X b))
  (@kernel_adjunction_family_func K C (@additive_preadditive C Prod t Add) t (@additive_terminal_object C Prod t
  Add) P (@one_cat_native_snake_gamma_diagram K C (@additive_preadditive C Prod t Add) C1 t
  (@additive_terminal_object C Prod t Add) T0 Q A B X D b c h)) (@one_cat_native_snake_kernel_second K C
  (@additive_preadditive C Prod t Add) C1 t (@additive_terminal_object C Prod t Add) T0 P Q A B X D b c h))
  (@comp_fapp0 (Functor_cat K C) (@one_cat_native_snake_first_cover_source K C (@additive_preadditive C Prod t
  Add) C1 t (@additive_terminal_object C Prod t Add) T0 P Q A B X D b c h) (@comp_cat_fapp0 K (Functor_cat
  WalkingArrow_cat C) C (@adjunction_image_func C (@additive_preadditive C Prod t Add) t
  (@additive_terminal_object C Prod t Add) T0 P Q) (@zero_arrow_family_incoming_func K C t
  (@additive_terminal_object C Prod t Add) (@kernel_adjunction_family_func K C (@additive_preadditive C Prod t
  Add) t (@additive_terminal_object C Prod t Add) P (@one_cat_native_snake_alpha_diagram K C
  (@additive_preadditive C Prod t Add) C1 t (@additive_terminal_object C Prod t Add) T0 P A B X D b c h))
  (@transf_arrow_diagram_func K C (@kernel_adjunction_family_func K C (@additive_preadditive C Prod t Add) t
  (@additive_terminal_object C Prod t Add) P (@transf_arrow_diagram_func K C B X b))
  (@kernel_adjunction_family_func K C (@additive_preadditive C Prod t Add) t (@additive_terminal_object C Prod t
  Add) P (@one_cat_native_snake_gamma_diagram K C (@additive_preadditive C Prod t Add) C1 t
  (@additive_terminal_object C Prod t Add) T0 Q A B X D b c h)) (@one_cat_native_snake_kernel_second K C
  (@additive_preadditive C Prod t Add) C1 t (@additive_terminal_object C Prod t Add) T0 P Q A B X D b c h))
  (@one_cat_native_snake_first_exact_input K C C1 Prod t Add T0 P Q N A B X D b c h)))
  (@kernel_adjunction_family_func K C (@additive_preadditive C Prod t Add) t (@additive_terminal_object C Prod t
  Add) P (@transf_arrow_diagram_func K C (@kernel_adjunction_family_func K C (@additive_preadditive C Prod t
  Add) t (@additive_terminal_object C Prod t Add) P (@transf_arrow_diagram_func K C B X b))
  (@kernel_adjunction_family_func K C (@additive_preadditive C Prod t Add) t (@additive_terminal_object C Prod t
  Add) P (@one_cat_native_snake_gamma_diagram K C (@additive_preadditive C Prod t Add) C1 t
  (@additive_terminal_object C Prod t Add) T0 Q A B X D b c h)) (@one_cat_native_snake_kernel_second K C
  (@additive_preadditive C Prod t Add) C1 t (@additive_terminal_object C Prod t Add) T0 P Q A B X D b c h)))
  (@one_cat_native_snake_first_exact_comparison K C C1 Prod t Add T0 P Q N A B X D b c h) (@comp_fapp0
  (Functor_cat K C) (@one_cat_native_snake_first_cover_source K C (@additive_preadditive C Prod t Add) C1 t
  (@additive_terminal_object C Prod t Add) T0 P Q A B X D b c h) (@kernel_adjunction_family_func K C
  (@additive_preadditive C Prod t Add) t (@additive_terminal_object C Prod t Add) P
  (@one_cat_native_snake_alpha_diagram K C (@additive_preadditive C Prod t Add) C1 t (@additive_terminal_object
  C Prod t Add) T0 P A B X D b c h)) (@comp_cat_fapp0 K (Functor_cat WalkingArrow_cat C) C
  (@adjunction_image_func C (@additive_preadditive C Prod t Add) t (@additive_terminal_object C Prod t Add) T0 P
  Q) (@zero_arrow_family_incoming_func K C t (@additive_terminal_object C Prod t Add)
  (@kernel_adjunction_family_func K C (@additive_preadditive C Prod t Add) t (@additive_terminal_object C Prod t
  Add) P (@one_cat_native_snake_alpha_diagram K C (@additive_preadditive C Prod t Add) C1 t
  (@additive_terminal_object C Prod t Add) T0 P A B X D b c h)) (@transf_arrow_diagram_func K C
  (@kernel_adjunction_family_func K C (@additive_preadditive C Prod t Add) t (@additive_terminal_object C Prod t
  Add) P (@transf_arrow_diagram_func K C B X b)) (@kernel_adjunction_family_func K C (@additive_preadditive C
  Prod t Add) t (@additive_terminal_object C Prod t Add) P (@one_cat_native_snake_gamma_diagram K C
  (@additive_preadditive C Prod t Add) C1 t (@additive_terminal_object C Prod t Add) T0 Q A B X D b c h))
  (@one_cat_native_snake_kernel_second K C (@additive_preadditive C Prod t Add) C1 t (@additive_terminal_object
  C Prod t Add) T0 P Q A B X D b c h)) (@one_cat_native_snake_first_exact_input K C C1 Prod t Add T0 P Q N A B X
  D b c h))) (@one_cat_image_family_source_transf K C (@additive_preadditive C Prod t Add) C1 t
  (@additive_terminal_object C Prod t Add) T0 P Q (@zero_arrow_family_incoming_func K C t
  (@additive_terminal_object C Prod t Add) (@kernel_adjunction_family_func K C (@additive_preadditive C Prod t
  Add) t (@additive_terminal_object C Prod t Add) P (@one_cat_native_snake_alpha_diagram K C
  (@additive_preadditive C Prod t Add) C1 t (@additive_terminal_object C Prod t Add) T0 P A B X D b c h))
  (@transf_arrow_diagram_func K C (@kernel_adjunction_family_func K C (@additive_preadditive C Prod t Add) t
  (@additive_terminal_object C Prod t Add) P (@transf_arrow_diagram_func K C B X b))
  (@kernel_adjunction_family_func K C (@additive_preadditive C Prod t Add) t (@additive_terminal_object C Prod t
  Add) P (@one_cat_native_snake_gamma_diagram K C (@additive_preadditive C Prod t Add) C1 t
  (@additive_terminal_object C Prod t Add) T0 Q A B X D b c h)) (@one_cat_native_snake_kernel_second K C
  (@additive_preadditive C Prod t Add) C1 t (@additive_terminal_object C Prod t Add) T0 P Q A B X D b c h))
  (@one_cat_native_snake_first_exact_input K C C1 Prod t Add T0 P Q N A B X D b c h)))
  (@one_cat_native_snake_first_cover_to_alpha_kernel K C (@additive_preadditive C Prod t Add) C1 t
  (@additive_terminal_object C Prod t Add) T0 P Q A B X D b c h))) (@comp_fapp0 (Functor_cat K C)
  (@one_cat_native_snake_first_cover_source K C (@additive_preadditive C Prod t Add) C1 t
  (@additive_terminal_object C Prod t Add) T0 P Q A B X D b c h) (@kernel_adjunction_family_func K C
  (@additive_preadditive C Prod t Add) t (@additive_terminal_object C Prod t Add) P (@transf_arrow_diagram_func
  K C (@one_cat_native_snake_image_func K C (@additive_preadditive C Prod t Add) C1 t (@additive_terminal_object
  C Prod t Add) T0 P Q A B X D b c h) (@kernel_adjunction_family_func K C (@additive_preadditive C Prod t Add) t
  (@additive_terminal_object C Prod t Add) P (@transf_arrow_diagram_func K C X D c))
  (@one_cat_native_snake_image_lift K C (@additive_preadditive C Prod t Add) C1 t (@additive_terminal_object C
  Prod t Add) T0 P Q A B X D b c h))) (@kernel_adjunction_family_func K C (@additive_preadditive C Prod t Add) t
  (@additive_terminal_object C Prod t Add) P (@transf_arrow_diagram_func K C (@kernel_adjunction_family_func K C
  (@additive_preadditive C Prod t Add) t (@additive_terminal_object C Prod t Add) P (@transf_arrow_diagram_func
  K C B X b)) (@kernel_adjunction_family_func K C (@additive_preadditive C Prod t Add) t
  (@additive_terminal_object C Prod t Add) P (@one_cat_native_snake_gamma_diagram K C (@additive_preadditive C
  Prod t Add) C1 t (@additive_terminal_object C Prod t Add) T0 Q A B X D b c h))
  (@one_cat_native_snake_kernel_second K C (@additive_preadditive C Prod t Add) C1 t (@additive_terminal_object
  C Prod t Add) T0 P Q A B X D b c h))) (@one_cat_native_snake_first_image_kernel_to_kernel K C
  (@additive_preadditive C Prod t Add) C1 t (@additive_terminal_object C Prod t Add) T0 P Q A B X D b c h)
  (@one_cat_native_snake_first_cover_transf K C (@additive_preadditive C Prod t Add) C1 t
  (@additive_terminal_object C Prod t Add) T0 P Q A B X D b c h)) (@eq_trans _ _ _ _ (@eq_ap (@Transf K C
  (@one_cat_native_snake_first_cover_source K C (@additive_preadditive C Prod t Add) C1 t
  (@additive_terminal_object C Prod t Add) T0 P Q A B X D b c h) (@kernel_adjunction_family_func K C
  (@additive_preadditive C Prod t Add) t (@additive_terminal_object C Prod t Add) P (@transf_arrow_diagram_func
  K C (@kernel_adjunction_family_func K C (@additive_preadditive C Prod t Add) t (@additive_terminal_object C
  Prod t Add) P (@transf_arrow_diagram_func K C B X b)) (@kernel_adjunction_family_func K C
  (@additive_preadditive C Prod t Add) t (@additive_terminal_object C Prod t Add) P
  (@one_cat_native_snake_gamma_diagram K C (@additive_preadditive C Prod t Add) C1 t (@additive_terminal_object
  C Prod t Add) T0 Q A B X D b c h)) (@one_cat_native_snake_kernel_second K C (@additive_preadditive C Prod t
  Add) C1 t (@additive_terminal_object C Prod t Add) T0 P Q A B X D b c h)))) (@Transf K C
  (@one_cat_native_snake_first_cover_source K C (@additive_preadditive C Prod t Add) C1 t
  (@additive_terminal_object C Prod t Add) T0 P Q A B X D b c h) (@kernel_adjunction_family_func K C
  (@additive_preadditive C Prod t Add) t (@additive_terminal_object C Prod t Add) P (@transf_arrow_diagram_func
  K C B X b))) (λ v : τ (@Transf K C (@one_cat_native_snake_first_cover_source K C (@additive_preadditive C Prod
  t Add) C1 t (@additive_terminal_object C Prod t Add) T0 P Q A B X D b c h) (@kernel_adjunction_family_func K C
  (@additive_preadditive C Prod t Add) t (@additive_terminal_object C Prod t Add) P (@transf_arrow_diagram_func
  K C (@kernel_adjunction_family_func K C (@additive_preadditive C Prod t Add) t (@additive_terminal_object C
  Prod t Add) P (@transf_arrow_diagram_func K C B X b)) (@kernel_adjunction_family_func K C
  (@additive_preadditive C Prod t Add) t (@additive_terminal_object C Prod t Add) P
  (@one_cat_native_snake_gamma_diagram K C (@additive_preadditive C Prod t Add) C1 t (@additive_terminal_object
  C Prod t Add) T0 Q A B X D b c h)) (@one_cat_native_snake_kernel_second K C (@additive_preadditive C Prod t
  Add) C1 t (@additive_terminal_object C Prod t Add) T0 P Q A B X D b c h)))), (@comp_fapp0 (Functor_cat K C)
  (@one_cat_native_snake_first_cover_source K C (@additive_preadditive C Prod t Add) C1 t
  (@additive_terminal_object C Prod t Add) T0 P Q A B X D b c h) (@kernel_adjunction_family_func K C
  (@additive_preadditive C Prod t Add) t (@additive_terminal_object C Prod t Add) P (@transf_arrow_diagram_func
  K C (@kernel_adjunction_family_func K C (@additive_preadditive C Prod t Add) t (@additive_terminal_object C
  Prod t Add) P (@transf_arrow_diagram_func K C B X b)) (@kernel_adjunction_family_func K C
  (@additive_preadditive C Prod t Add) t (@additive_terminal_object C Prod t Add) P
  (@one_cat_native_snake_gamma_diagram K C (@additive_preadditive C Prod t Add) C1 t (@additive_terminal_object
  C Prod t Add) T0 Q A B X D b c h)) (@one_cat_native_snake_kernel_second K C (@additive_preadditive C Prod t
  Add) C1 t (@additive_terminal_object C Prod t Add) T0 P Q A B X D b c h))) (@kernel_adjunction_family_func K C
  (@additive_preadditive C Prod t Add) t (@additive_terminal_object C Prod t Add) P (@transf_arrow_diagram_func
  K C B X b)) (@kernel_adjunction_family_inclusion_transf K C (@additive_preadditive C Prod t Add) t
  (@additive_terminal_object C Prod t Add) P (@transf_arrow_diagram_func K C (@kernel_adjunction_family_func K C
  (@additive_preadditive C Prod t Add) t (@additive_terminal_object C Prod t Add) P (@transf_arrow_diagram_func
  K C B X b)) (@kernel_adjunction_family_func K C (@additive_preadditive C Prod t Add) t
  (@additive_terminal_object C Prod t Add) P (@one_cat_native_snake_gamma_diagram K C (@additive_preadditive C
  Prod t Add) C1 t (@additive_terminal_object C Prod t Add) T0 Q A B X D b c h))
  (@one_cat_native_snake_kernel_second K C (@additive_preadditive C Prod t Add) C1 t (@additive_terminal_object
  C Prod t Add) T0 P Q A B X D b c h))) v)) _ _ (@comp_assoc (Functor_cat K C)
  (@one_cat_native_snake_first_cover_source K C (@additive_preadditive C Prod t Add) C1 t
  (@additive_terminal_object C Prod t Add) T0 P Q A B X D b c h) (@kernel_adjunction_family_func K C
  (@additive_preadditive C Prod t Add) t (@additive_terminal_object C Prod t Add) P
  (@one_cat_native_snake_alpha_diagram K C (@additive_preadditive C Prod t Add) C1 t (@additive_terminal_object
  C Prod t Add) T0 P A B X D b c h)) (@comp_cat_fapp0 K (Functor_cat WalkingArrow_cat C) C
  (@adjunction_image_func C (@additive_preadditive C Prod t Add) t (@additive_terminal_object C Prod t Add) T0 P
  Q) (@zero_arrow_family_incoming_func K C t (@additive_terminal_object C Prod t Add)
  (@kernel_adjunction_family_func K C (@additive_preadditive C Prod t Add) t (@additive_terminal_object C Prod t
  Add) P (@one_cat_native_snake_alpha_diagram K C (@additive_preadditive C Prod t Add) C1 t
  (@additive_terminal_object C Prod t Add) T0 P A B X D b c h)) (@transf_arrow_diagram_func K C
  (@kernel_adjunction_family_func K C (@additive_preadditive C Prod t Add) t (@additive_terminal_object C Prod t
  Add) P (@transf_arrow_diagram_func K C B X b)) (@kernel_adjunction_family_func K C (@additive_preadditive C
  Prod t Add) t (@additive_terminal_object C Prod t Add) P (@one_cat_native_snake_gamma_diagram K C
  (@additive_preadditive C Prod t Add) C1 t (@additive_terminal_object C Prod t Add) T0 Q A B X D b c h))
  (@one_cat_native_snake_kernel_second K C (@additive_preadditive C Prod t Add) C1 t (@additive_terminal_object
  C Prod t Add) T0 P Q A B X D b c h)) (@one_cat_native_snake_first_exact_input K C C1 Prod t Add T0 P Q N A B X
  D b c h))) (@kernel_adjunction_family_func K C (@additive_preadditive C Prod t Add) t
  (@additive_terminal_object C Prod t Add) P (@transf_arrow_diagram_func K C (@kernel_adjunction_family_func K C
  (@additive_preadditive C Prod t Add) t (@additive_terminal_object C Prod t Add) P (@transf_arrow_diagram_func
  K C B X b)) (@kernel_adjunction_family_func K C (@additive_preadditive C Prod t Add) t
  (@additive_terminal_object C Prod t Add) P (@one_cat_native_snake_gamma_diagram K C (@additive_preadditive C
  Prod t Add) C1 t (@additive_terminal_object C Prod t Add) T0 Q A B X D b c h))
  (@one_cat_native_snake_kernel_second K C (@additive_preadditive C Prod t Add) C1 t (@additive_terminal_object
  C Prod t Add) T0 P Q A B X D b c h))) (@one_cat_native_snake_first_exact_comparison K C C1 Prod t Add T0 P Q N
  A B X D b c h) (@one_cat_image_family_source_transf K C (@additive_preadditive C Prod t Add) C1 t
  (@additive_terminal_object C Prod t Add) T0 P Q (@zero_arrow_family_incoming_func K C t
  (@additive_terminal_object C Prod t Add) (@kernel_adjunction_family_func K C (@additive_preadditive C Prod t
  Add) t (@additive_terminal_object C Prod t Add) P (@one_cat_native_snake_alpha_diagram K C
  (@additive_preadditive C Prod t Add) C1 t (@additive_terminal_object C Prod t Add) T0 P A B X D b c h))
  (@transf_arrow_diagram_func K C (@kernel_adjunction_family_func K C (@additive_preadditive C Prod t Add) t
  (@additive_terminal_object C Prod t Add) P (@transf_arrow_diagram_func K C B X b))
  (@kernel_adjunction_family_func K C (@additive_preadditive C Prod t Add) t (@additive_terminal_object C Prod t
  Add) P (@one_cat_native_snake_gamma_diagram K C (@additive_preadditive C Prod t Add) C1 t
  (@additive_terminal_object C Prod t Add) T0 Q A B X D b c h)) (@one_cat_native_snake_kernel_second K C
  (@additive_preadditive C Prod t Add) C1 t (@additive_terminal_object C Prod t Add) T0 P Q A B X D b c h))
  (@one_cat_native_snake_first_exact_input K C C1 Prod t Add T0 P Q N A B X D b c h)))
  (@one_cat_native_snake_first_cover_to_alpha_kernel K C (@additive_preadditive C Prod t Add) C1 t
  (@additive_terminal_object C Prod t Add) T0 P Q A B X D b c h))) (@eq_trans _ _ _ _ (@comp_assoc (Functor_cat
  K C) (@one_cat_native_snake_first_cover_source K C (@additive_preadditive C Prod t Add) C1 t
  (@additive_terminal_object C Prod t Add) T0 P Q A B X D b c h) (@kernel_adjunction_family_func K C
  (@additive_preadditive C Prod t Add) t (@additive_terminal_object C Prod t Add) P
  (@one_cat_native_snake_alpha_diagram K C (@additive_preadditive C Prod t Add) C1 t (@additive_terminal_object
  C Prod t Add) T0 P A B X D b c h)) (@kernel_adjunction_family_func K C (@additive_preadditive C Prod t Add) t
  (@additive_terminal_object C Prod t Add) P (@transf_arrow_diagram_func K C (@kernel_adjunction_family_func K C
  (@additive_preadditive C Prod t Add) t (@additive_terminal_object C Prod t Add) P (@transf_arrow_diagram_func
  K C B X b)) (@kernel_adjunction_family_func K C (@additive_preadditive C Prod t Add) t
  (@additive_terminal_object C Prod t Add) P (@one_cat_native_snake_gamma_diagram K C (@additive_preadditive C
  Prod t Add) C1 t (@additive_terminal_object C Prod t Add) T0 Q A B X D b c h))
  (@one_cat_native_snake_kernel_second K C (@additive_preadditive C Prod t Add) C1 t (@additive_terminal_object
  C Prod t Add) T0 P Q A B X D b c h))) (@kernel_adjunction_family_func K C (@additive_preadditive C Prod t Add)
  t (@additive_terminal_object C Prod t Add) P (@transf_arrow_diagram_func K C B X b))
  (@kernel_adjunction_family_inclusion_transf K C (@additive_preadditive C Prod t Add) t
  (@additive_terminal_object C Prod t Add) P (@transf_arrow_diagram_func K C (@kernel_adjunction_family_func K C
  (@additive_preadditive C Prod t Add) t (@additive_terminal_object C Prod t Add) P (@transf_arrow_diagram_func
  K C B X b)) (@kernel_adjunction_family_func K C (@additive_preadditive C Prod t Add) t
  (@additive_terminal_object C Prod t Add) P (@one_cat_native_snake_gamma_diagram K C (@additive_preadditive C
  Prod t Add) C1 t (@additive_terminal_object C Prod t Add) T0 Q A B X D b c h))
  (@one_cat_native_snake_kernel_second K C (@additive_preadditive C Prod t Add) C1 t (@additive_terminal_object
  C Prod t Add) T0 P Q A B X D b c h))) (@comp_fapp0 (Functor_cat K C) (@kernel_adjunction_family_func K C
  (@additive_preadditive C Prod t Add) t (@additive_terminal_object C Prod t Add) P
  (@one_cat_native_snake_alpha_diagram K C (@additive_preadditive C Prod t Add) C1 t (@additive_terminal_object
  C Prod t Add) T0 P A B X D b c h)) (@comp_cat_fapp0 K (Functor_cat WalkingArrow_cat C) C
  (@adjunction_image_func C (@additive_preadditive C Prod t Add) t (@additive_terminal_object C Prod t Add) T0 P
  Q) (@zero_arrow_family_incoming_func K C t (@additive_terminal_object C Prod t Add)
  (@kernel_adjunction_family_func K C (@additive_preadditive C Prod t Add) t (@additive_terminal_object C Prod t
  Add) P (@one_cat_native_snake_alpha_diagram K C (@additive_preadditive C Prod t Add) C1 t
  (@additive_terminal_object C Prod t Add) T0 P A B X D b c h)) (@transf_arrow_diagram_func K C
  (@kernel_adjunction_family_func K C (@additive_preadditive C Prod t Add) t (@additive_terminal_object C Prod t
  Add) P (@transf_arrow_diagram_func K C B X b)) (@kernel_adjunction_family_func K C (@additive_preadditive C
  Prod t Add) t (@additive_terminal_object C Prod t Add) P (@one_cat_native_snake_gamma_diagram K C
  (@additive_preadditive C Prod t Add) C1 t (@additive_terminal_object C Prod t Add) T0 Q A B X D b c h))
  (@one_cat_native_snake_kernel_second K C (@additive_preadditive C Prod t Add) C1 t (@additive_terminal_object
  C Prod t Add) T0 P Q A B X D b c h)) (@one_cat_native_snake_first_exact_input K C C1 Prod t Add T0 P Q N A B X
  D b c h))) (@kernel_adjunction_family_func K C (@additive_preadditive C Prod t Add) t
  (@additive_terminal_object C Prod t Add) P (@transf_arrow_diagram_func K C (@kernel_adjunction_family_func K C
  (@additive_preadditive C Prod t Add) t (@additive_terminal_object C Prod t Add) P (@transf_arrow_diagram_func
  K C B X b)) (@kernel_adjunction_family_func K C (@additive_preadditive C Prod t Add) t
  (@additive_terminal_object C Prod t Add) P (@one_cat_native_snake_gamma_diagram K C (@additive_preadditive C
  Prod t Add) C1 t (@additive_terminal_object C Prod t Add) T0 Q A B X D b c h))
  (@one_cat_native_snake_kernel_second K C (@additive_preadditive C Prod t Add) C1 t (@additive_terminal_object
  C Prod t Add) T0 P Q A B X D b c h))) (@one_cat_native_snake_first_exact_comparison K C C1 Prod t Add T0 P Q N
  A B X D b c h) (@one_cat_image_family_source_transf K C (@additive_preadditive C Prod t Add) C1 t
  (@additive_terminal_object C Prod t Add) T0 P Q (@zero_arrow_family_incoming_func K C t
  (@additive_terminal_object C Prod t Add) (@kernel_adjunction_family_func K C (@additive_preadditive C Prod t
  Add) t (@additive_terminal_object C Prod t Add) P (@one_cat_native_snake_alpha_diagram K C
  (@additive_preadditive C Prod t Add) C1 t (@additive_terminal_object C Prod t Add) T0 P A B X D b c h))
  (@transf_arrow_diagram_func K C (@kernel_adjunction_family_func K C (@additive_preadditive C Prod t Add) t
  (@additive_terminal_object C Prod t Add) P (@transf_arrow_diagram_func K C B X b))
  (@kernel_adjunction_family_func K C (@additive_preadditive C Prod t Add) t (@additive_terminal_object C Prod t
  Add) P (@one_cat_native_snake_gamma_diagram K C (@additive_preadditive C Prod t Add) C1 t
  (@additive_terminal_object C Prod t Add) T0 Q A B X D b c h)) (@one_cat_native_snake_kernel_second K C
  (@additive_preadditive C Prod t Add) C1 t (@additive_terminal_object C Prod t Add) T0 P Q A B X D b c h))
  (@one_cat_native_snake_first_exact_input K C C1 Prod t Add T0 P Q N A B X D b c h))))
  (@one_cat_native_snake_first_cover_to_alpha_kernel K C (@additive_preadditive C Prod t Add) C1 t
  (@additive_terminal_object C Prod t Add) T0 P Q A B X D b c h)) (@eq_trans _ _ _ _ (@eq_ap (@Transf K C
  (@kernel_adjunction_family_func K C (@additive_preadditive C Prod t Add) t (@additive_terminal_object C Prod t
  Add) P (@one_cat_native_snake_alpha_diagram K C (@additive_preadditive C Prod t Add) C1 t
  (@additive_terminal_object C Prod t Add) T0 P A B X D b c h)) (@kernel_adjunction_family_func K C
  (@additive_preadditive C Prod t Add) t (@additive_terminal_object C Prod t Add) P (@transf_arrow_diagram_func
  K C B X b))) (@Transf K C (@one_cat_native_snake_first_cover_source K C (@additive_preadditive C Prod t Add)
  C1 t (@additive_terminal_object C Prod t Add) T0 P Q A B X D b c h) (@kernel_adjunction_family_func K C
  (@additive_preadditive C Prod t Add) t (@additive_terminal_object C Prod t Add) P (@transf_arrow_diagram_func
  K C B X b))) (λ v : τ (@Transf K C (@kernel_adjunction_family_func K C (@additive_preadditive C Prod t Add) t
  (@additive_terminal_object C Prod t Add) P (@one_cat_native_snake_alpha_diagram K C (@additive_preadditive C
  Prod t Add) C1 t (@additive_terminal_object C Prod t Add) T0 P A B X D b c h)) (@kernel_adjunction_family_func
  K C (@additive_preadditive C Prod t Add) t (@additive_terminal_object C Prod t Add) P
  (@transf_arrow_diagram_func K C B X b))), (@comp_fapp0 (Functor_cat K C)
  (@one_cat_native_snake_first_cover_source K C (@additive_preadditive C Prod t Add) C1 t
  (@additive_terminal_object C Prod t Add) T0 P Q A B X D b c h) (@kernel_adjunction_family_func K C
  (@additive_preadditive C Prod t Add) t (@additive_terminal_object C Prod t Add) P
  (@one_cat_native_snake_alpha_diagram K C (@additive_preadditive C Prod t Add) C1 t (@additive_terminal_object
  C Prod t Add) T0 P A B X D b c h)) (@kernel_adjunction_family_func K C (@additive_preadditive C Prod t Add) t
  (@additive_terminal_object C Prod t Add) P (@transf_arrow_diagram_func K C B X b)) v
  (@one_cat_native_snake_first_cover_to_alpha_kernel K C (@additive_preadditive C Prod t Add) C1 t
  (@additive_terminal_object C Prod t Add) T0 P Q A B X D b c h))) _ _
  (@one_cat_native_snake_first_comparison_source_path K C C1 Prod t Add T0 P Q N A B X D b c h)) (@eq_trans _ _
  _ _ (@one_cat_native_snake_first_cover_middle_path K C C1 Prod t Add T0 P Q N A B X D b c h) (@eq_trans _ _ _
  _ (@eq_ap (@Transf K C (@kernel_adjunction_family_func K C (@additive_preadditive C Prod t Add) t
  (@additive_terminal_object C Prod t Add) P (@transf_arrow_diagram_func K C (@one_cat_native_snake_image_func K
  C (@additive_preadditive C Prod t Add) C1 t (@additive_terminal_object C Prod t Add) T0 P Q A B X D b c h)
  (@kernel_adjunction_family_func K C (@additive_preadditive C Prod t Add) t (@additive_terminal_object C Prod t
  Add) P (@transf_arrow_diagram_func K C X D c)) (@one_cat_native_snake_image_lift K C (@additive_preadditive C
  Prod t Add) C1 t (@additive_terminal_object C Prod t Add) T0 P Q A B X D b c h)))
  (@kernel_adjunction_family_func K C (@additive_preadditive C Prod t Add) t (@additive_terminal_object C Prod t
  Add) P (@transf_arrow_diagram_func K C B X b))) (@Transf K C (@one_cat_native_snake_first_cover_source K C
  (@additive_preadditive C Prod t Add) C1 t (@additive_terminal_object C Prod t Add) T0 P Q A B X D b c h)
  (@kernel_adjunction_family_func K C (@additive_preadditive C Prod t Add) t (@additive_terminal_object C Prod t
  Add) P (@transf_arrow_diagram_func K C B X b))) (λ v : τ (@Transf K C (@kernel_adjunction_family_func K C
  (@additive_preadditive C Prod t Add) t (@additive_terminal_object C Prod t Add) P (@transf_arrow_diagram_func
  K C (@one_cat_native_snake_image_func K C (@additive_preadditive C Prod t Add) C1 t (@additive_terminal_object
  C Prod t Add) T0 P Q A B X D b c h) (@kernel_adjunction_family_func K C (@additive_preadditive C Prod t Add) t
  (@additive_terminal_object C Prod t Add) P (@transf_arrow_diagram_func K C X D c))
  (@one_cat_native_snake_image_lift K C (@additive_preadditive C Prod t Add) C1 t (@additive_terminal_object C
  Prod t Add) T0 P Q A B X D b c h))) (@kernel_adjunction_family_func K C (@additive_preadditive C Prod t Add) t
  (@additive_terminal_object C Prod t Add) P (@transf_arrow_diagram_func K C B X b))), (@comp_fapp0 (Functor_cat
  K C) (@one_cat_native_snake_first_cover_source K C (@additive_preadditive C Prod t Add) C1 t
  (@additive_terminal_object C Prod t Add) T0 P Q A B X D b c h) (@kernel_adjunction_family_func K C
  (@additive_preadditive C Prod t Add) t (@additive_terminal_object C Prod t Add) P (@transf_arrow_diagram_func
  K C (@one_cat_native_snake_image_func K C (@additive_preadditive C Prod t Add) C1 t (@additive_terminal_object
  C Prod t Add) T0 P Q A B X D b c h) (@kernel_adjunction_family_func K C (@additive_preadditive C Prod t Add) t
  (@additive_terminal_object C Prod t Add) P (@transf_arrow_diagram_func K C X D c))
  (@one_cat_native_snake_image_lift K C (@additive_preadditive C Prod t Add) C1 t (@additive_terminal_object C
  Prod t Add) T0 P Q A B X D b c h))) (@kernel_adjunction_family_func K C (@additive_preadditive C Prod t Add) t
  (@additive_terminal_object C Prod t Add) P (@transf_arrow_diagram_func K C B X b)) v
  (@one_cat_native_snake_first_cover_transf K C (@additive_preadditive C Prod t Add) C1 t
  (@additive_terminal_object C Prod t Add) T0 P Q A B X D b c h))) _ _ (@eq_sym _ _ _
  (@one_cat_native_snake_first_image_kernel_kernel_reconstruction K C (@additive_preadditive C Prod t Add) C1 t
  (@additive_terminal_object C Prod t Add) T0 P Q A B X D b c h))) (@eq_sym _ _ _ (@comp_assoc (Functor_cat K C)
  (@one_cat_native_snake_first_cover_source K C (@additive_preadditive C Prod t Add) C1 t
  (@additive_terminal_object C Prod t Add) T0 P Q A B X D b c h) (@kernel_adjunction_family_func K C
  (@additive_preadditive C Prod t Add) t (@additive_terminal_object C Prod t Add) P (@transf_arrow_diagram_func
  K C (@one_cat_native_snake_image_func K C (@additive_preadditive C Prod t Add) C1 t (@additive_terminal_object
  C Prod t Add) T0 P Q A B X D b c h) (@kernel_adjunction_family_func K C (@additive_preadditive C Prod t Add) t
  (@additive_terminal_object C Prod t Add) P (@transf_arrow_diagram_func K C X D c))
  (@one_cat_native_snake_image_lift K C (@additive_preadditive C Prod t Add) C1 t (@additive_terminal_object C
  Prod t Add) T0 P Q A B X D b c h))) (@kernel_adjunction_family_func K C (@additive_preadditive C Prod t Add) t
  (@additive_terminal_object C Prod t Add) P (@transf_arrow_diagram_func K C (@kernel_adjunction_family_func K C
  (@additive_preadditive C Prod t Add) t (@additive_terminal_object C Prod t Add) P (@transf_arrow_diagram_func
  K C B X b)) (@kernel_adjunction_family_func K C (@additive_preadditive C Prod t Add) t
  (@additive_terminal_object C Prod t Add) P (@one_cat_native_snake_gamma_diagram K C (@additive_preadditive C
  Prod t Add) C1 t (@additive_terminal_object C Prod t Add) T0 Q A B X D b c h))
  (@one_cat_native_snake_kernel_second K C (@additive_preadditive C Prod t Add) C1 t (@additive_terminal_object
  C Prod t Add) T0 P Q A B X D b c h))) (@kernel_adjunction_family_func K C (@additive_preadditive C Prod t Add)
  t (@additive_terminal_object C Prod t Add) P (@transf_arrow_diagram_func K C B X b))
  (@kernel_adjunction_family_inclusion_transf K C (@additive_preadditive C Prod t Add) t
  (@additive_terminal_object C Prod t Add) P (@transf_arrow_diagram_func K C (@kernel_adjunction_family_func K C
  (@additive_preadditive C Prod t Add) t (@additive_terminal_object C Prod t Add) P (@transf_arrow_diagram_func
  K C B X b)) (@kernel_adjunction_family_func K C (@additive_preadditive C Prod t Add) t
  (@additive_terminal_object C Prod t Add) P (@one_cat_native_snake_gamma_diagram K C (@additive_preadditive C
  Prod t Add) C1 t (@additive_terminal_object C Prod t Add) T0 Q A B X D b c h))
  (@one_cat_native_snake_kernel_second K C (@additive_preadditive C Prod t Add) C1 t (@additive_terminal_object
  C Prod t Add) T0 P Q A B X D b c h))) (@one_cat_native_snake_first_image_kernel_to_kernel K C
  (@additive_preadditive C Prod t Add) C1 t (@additive_terminal_object C Prod t Add) T0 P Q A B X D b c h)
  (@one_cat_native_snake_first_cover_transf K C (@additive_preadditive C Prod t Add) C1 t
  (@additive_terminal_object C Prod t Add) T0 P Q A B X D b c h)))))))));

// The original cover cancellation makes π_eη zero.
symbol one_cat_native_snake_first_cokernel_after_retraction_zero [K C : Cat]
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
  : τ (@= (@Transf K C (@kernel_adjunction_family_func K C (@additive_preadditive C Prod t Add) t
    (@additive_terminal_object C Prod t Add) P (@transf_arrow_diagram_func K C (@one_cat_native_snake_image_func
    K C (@additive_preadditive C Prod t Add) C1 t (@additive_terminal_object C Prod t Add) T0 P Q A B X D b c h)
    (@kernel_adjunction_family_func K C (@additive_preadditive C Prod t Add) t (@additive_terminal_object C Prod
    t Add) P (@transf_arrow_diagram_func K C X D c)) (@one_cat_native_snake_image_lift K C
    (@additive_preadditive C Prod t Add) C1 t (@additive_terminal_object C Prod t Add) T0 P Q A B X D b c h)))
    (@cokernel_adjunction_family_func K C (@additive_preadditive C Prod t Add) t T0 Q
    (@transf_arrow_diagram_func K C (@comp_cat_fapp0 K (Functor_cat WalkingArrow_cat C) C
    (@adjunction_image_func C (@additive_preadditive C Prod t Add) t (@additive_terminal_object C Prod t Add) T0
    P Q) (@zero_arrow_family_incoming_func K C t (@additive_terminal_object C Prod t Add)
    (@kernel_adjunction_family_func K C (@additive_preadditive C Prod t Add) t (@additive_terminal_object C Prod
    t Add) P (@one_cat_native_snake_alpha_diagram K C (@additive_preadditive C Prod t Add) C1 t
    (@additive_terminal_object C Prod t Add) T0 P A B X D b c h)) (@transf_arrow_diagram_func K C
    (@kernel_adjunction_family_func K C (@additive_preadditive C Prod t Add) t (@additive_terminal_object C Prod
    t Add) P (@transf_arrow_diagram_func K C B X b)) (@kernel_adjunction_family_func K C (@additive_preadditive
    C Prod t Add) t (@additive_terminal_object C Prod t Add) P (@one_cat_native_snake_gamma_diagram K C
    (@additive_preadditive C Prod t Add) C1 t (@additive_terminal_object C Prod t Add) T0 Q A B X D b c h))
    (@one_cat_native_snake_kernel_second K C (@additive_preadditive C Prod t Add) C1 t
    (@additive_terminal_object C Prod t Add) T0 P Q A B X D b c h)) (@one_cat_native_snake_first_exact_input K C
    C1 Prod t Add T0 P Q N A B X D b c h))) (@kernel_adjunction_family_func K C (@additive_preadditive C Prod t
    Add) t (@additive_terminal_object C Prod t Add) P (@transf_arrow_diagram_func K C
    (@kernel_adjunction_family_func K C (@additive_preadditive C Prod t Add) t (@additive_terminal_object C Prod
    t Add) P (@transf_arrow_diagram_func K C B X b)) (@kernel_adjunction_family_func K C (@additive_preadditive
    C Prod t Add) t (@additive_terminal_object C Prod t Add) P (@one_cat_native_snake_gamma_diagram K C
    (@additive_preadditive C Prod t Add) C1 t (@additive_terminal_object C Prod t Add) T0 Q A B X D b c h))
    (@one_cat_native_snake_kernel_second K C (@additive_preadditive C Prod t Add) C1 t
    (@additive_terminal_object C Prod t Add) T0 P Q A B X D b c h)))
    (@one_cat_native_snake_first_exact_comparison K C C1 Prod t Add T0 P Q N A B X D b c h)))) (@comp_fapp0
    (Functor_cat K C) (@kernel_adjunction_family_func K C (@additive_preadditive C Prod t Add) t
    (@additive_terminal_object C Prod t Add) P (@transf_arrow_diagram_func K C (@one_cat_native_snake_image_func
    K C (@additive_preadditive C Prod t Add) C1 t (@additive_terminal_object C Prod t Add) T0 P Q A B X D b c h)
    (@kernel_adjunction_family_func K C (@additive_preadditive C Prod t Add) t (@additive_terminal_object C Prod
    t Add) P (@transf_arrow_diagram_func K C X D c)) (@one_cat_native_snake_image_lift K C
    (@additive_preadditive C Prod t Add) C1 t (@additive_terminal_object C Prod t Add) T0 P Q A B X D b c h)))
    (@kernel_adjunction_family_func K C (@additive_preadditive C Prod t Add) t (@additive_terminal_object C Prod
    t Add) P (@transf_arrow_diagram_func K C (@kernel_adjunction_family_func K C (@additive_preadditive C Prod t
    Add) t (@additive_terminal_object C Prod t Add) P (@transf_arrow_diagram_func K C B X b))
    (@kernel_adjunction_family_func K C (@additive_preadditive C Prod t Add) t (@additive_terminal_object C Prod
    t Add) P (@one_cat_native_snake_gamma_diagram K C (@additive_preadditive C Prod t Add) C1 t
    (@additive_terminal_object C Prod t Add) T0 Q A B X D b c h)) (@one_cat_native_snake_kernel_second K C
    (@additive_preadditive C Prod t Add) C1 t (@additive_terminal_object C Prod t Add) T0 P Q A B X D b c h)))
    (@cokernel_adjunction_family_func K C (@additive_preadditive C Prod t Add) t T0 Q
    (@transf_arrow_diagram_func K C (@comp_cat_fapp0 K (Functor_cat WalkingArrow_cat C) C
    (@adjunction_image_func C (@additive_preadditive C Prod t Add) t (@additive_terminal_object C Prod t Add) T0
    P Q) (@zero_arrow_family_incoming_func K C t (@additive_terminal_object C Prod t Add)
    (@kernel_adjunction_family_func K C (@additive_preadditive C Prod t Add) t (@additive_terminal_object C Prod
    t Add) P (@one_cat_native_snake_alpha_diagram K C (@additive_preadditive C Prod t Add) C1 t
    (@additive_terminal_object C Prod t Add) T0 P A B X D b c h)) (@transf_arrow_diagram_func K C
    (@kernel_adjunction_family_func K C (@additive_preadditive C Prod t Add) t (@additive_terminal_object C Prod
    t Add) P (@transf_arrow_diagram_func K C B X b)) (@kernel_adjunction_family_func K C (@additive_preadditive
    C Prod t Add) t (@additive_terminal_object C Prod t Add) P (@one_cat_native_snake_gamma_diagram K C
    (@additive_preadditive C Prod t Add) C1 t (@additive_terminal_object C Prod t Add) T0 Q A B X D b c h))
    (@one_cat_native_snake_kernel_second K C (@additive_preadditive C Prod t Add) C1 t
    (@additive_terminal_object C Prod t Add) T0 P Q A B X D b c h)) (@one_cat_native_snake_first_exact_input K C
    C1 Prod t Add T0 P Q N A B X D b c h))) (@kernel_adjunction_family_func K C (@additive_preadditive C Prod t
    Add) t (@additive_terminal_object C Prod t Add) P (@transf_arrow_diagram_func K C
    (@kernel_adjunction_family_func K C (@additive_preadditive C Prod t Add) t (@additive_terminal_object C Prod
    t Add) P (@transf_arrow_diagram_func K C B X b)) (@kernel_adjunction_family_func K C (@additive_preadditive
    C Prod t Add) t (@additive_terminal_object C Prod t Add) P (@one_cat_native_snake_gamma_diagram K C
    (@additive_preadditive C Prod t Add) C1 t (@additive_terminal_object C Prod t Add) T0 Q A B X D b c h))
    (@one_cat_native_snake_kernel_second K C (@additive_preadditive C Prod t Add) C1 t
    (@additive_terminal_object C Prod t Add) T0 P Q A B X D b c h)))
    (@one_cat_native_snake_first_exact_comparison K C C1 Prod t Add T0 P Q N A B X D b c h)))
    (@cokernel_adjunction_family_projection_transf K C (@additive_preadditive C Prod t Add) t T0 Q
    (@transf_arrow_diagram_func K C (@comp_cat_fapp0 K (Functor_cat WalkingArrow_cat C) C
    (@adjunction_image_func C (@additive_preadditive C Prod t Add) t (@additive_terminal_object C Prod t Add) T0
    P Q) (@zero_arrow_family_incoming_func K C t (@additive_terminal_object C Prod t Add)
    (@kernel_adjunction_family_func K C (@additive_preadditive C Prod t Add) t (@additive_terminal_object C Prod
    t Add) P (@one_cat_native_snake_alpha_diagram K C (@additive_preadditive C Prod t Add) C1 t
    (@additive_terminal_object C Prod t Add) T0 P A B X D b c h)) (@transf_arrow_diagram_func K C
    (@kernel_adjunction_family_func K C (@additive_preadditive C Prod t Add) t (@additive_terminal_object C Prod
    t Add) P (@transf_arrow_diagram_func K C B X b)) (@kernel_adjunction_family_func K C (@additive_preadditive
    C Prod t Add) t (@additive_terminal_object C Prod t Add) P (@one_cat_native_snake_gamma_diagram K C
    (@additive_preadditive C Prod t Add) C1 t (@additive_terminal_object C Prod t Add) T0 Q A B X D b c h))
    (@one_cat_native_snake_kernel_second K C (@additive_preadditive C Prod t Add) C1 t
    (@additive_terminal_object C Prod t Add) T0 P Q A B X D b c h)) (@one_cat_native_snake_first_exact_input K C
    C1 Prod t Add T0 P Q N A B X D b c h))) (@kernel_adjunction_family_func K C (@additive_preadditive C Prod t
    Add) t (@additive_terminal_object C Prod t Add) P (@transf_arrow_diagram_func K C
    (@kernel_adjunction_family_func K C (@additive_preadditive C Prod t Add) t (@additive_terminal_object C Prod
    t Add) P (@transf_arrow_diagram_func K C B X b)) (@kernel_adjunction_family_func K C (@additive_preadditive
    C Prod t Add) t (@additive_terminal_object C Prod t Add) P (@one_cat_native_snake_gamma_diagram K C
    (@additive_preadditive C Prod t Add) C1 t (@additive_terminal_object C Prod t Add) T0 Q A B X D b c h))
    (@one_cat_native_snake_kernel_second K C (@additive_preadditive C Prod t Add) C1 t
    (@additive_terminal_object C Prod t Add) T0 P Q A B X D b c h)))
    (@one_cat_native_snake_first_exact_comparison K C C1 Prod t Add T0 P Q N A B X D b c h)))
    (@one_cat_native_snake_first_image_kernel_to_kernel K C (@additive_preadditive C Prod t Add) C1 t
    (@additive_terminal_object C Prod t Add) T0 P Q A B X D b c h)) (@zero_arrow_family_zero_transf K C t
    (@additive_terminal_object C Prod t Add) T0 (@kernel_adjunction_family_func K C (@additive_preadditive C
    Prod t Add) t (@additive_terminal_object C Prod t Add) P (@transf_arrow_diagram_func K C
    (@one_cat_native_snake_image_func K C (@additive_preadditive C Prod t Add) C1 t (@additive_terminal_object C
    Prod t Add) T0 P Q A B X D b c h) (@kernel_adjunction_family_func K C (@additive_preadditive C Prod t Add) t
    (@additive_terminal_object C Prod t Add) P (@transf_arrow_diagram_func K C X D c))
    (@one_cat_native_snake_image_lift K C (@additive_preadditive C Prod t Add) C1 t (@additive_terminal_object C
    Prod t Add) T0 P Q A B X D b c h))) (@cokernel_adjunction_family_func K C (@additive_preadditive C Prod t
    Add) t T0 Q (@transf_arrow_diagram_func K C (@comp_cat_fapp0 K (Functor_cat WalkingArrow_cat C) C
    (@adjunction_image_func C (@additive_preadditive C Prod t Add) t (@additive_terminal_object C Prod t Add) T0
    P Q) (@zero_arrow_family_incoming_func K C t (@additive_terminal_object C Prod t Add)
    (@kernel_adjunction_family_func K C (@additive_preadditive C Prod t Add) t (@additive_terminal_object C Prod
    t Add) P (@one_cat_native_snake_alpha_diagram K C (@additive_preadditive C Prod t Add) C1 t
    (@additive_terminal_object C Prod t Add) T0 P A B X D b c h)) (@transf_arrow_diagram_func K C
    (@kernel_adjunction_family_func K C (@additive_preadditive C Prod t Add) t (@additive_terminal_object C Prod
    t Add) P (@transf_arrow_diagram_func K C B X b)) (@kernel_adjunction_family_func K C (@additive_preadditive
    C Prod t Add) t (@additive_terminal_object C Prod t Add) P (@one_cat_native_snake_gamma_diagram K C
    (@additive_preadditive C Prod t Add) C1 t (@additive_terminal_object C Prod t Add) T0 Q A B X D b c h))
    (@one_cat_native_snake_kernel_second K C (@additive_preadditive C Prod t Add) C1 t
    (@additive_terminal_object C Prod t Add) T0 P Q A B X D b c h)) (@one_cat_native_snake_first_exact_input K C
    C1 Prod t Add T0 P Q N A B X D b c h))) (@kernel_adjunction_family_func K C (@additive_preadditive C Prod t
    Add) t (@additive_terminal_object C Prod t Add) P (@transf_arrow_diagram_func K C
    (@kernel_adjunction_family_func K C (@additive_preadditive C Prod t Add) t (@additive_terminal_object C Prod
    t Add) P (@transf_arrow_diagram_func K C B X b)) (@kernel_adjunction_family_func K C (@additive_preadditive
    C Prod t Add) t (@additive_terminal_object C Prod t Add) P (@one_cat_native_snake_gamma_diagram K C
    (@additive_preadditive C Prod t Add) C1 t (@additive_terminal_object C Prod t Add) T0 Q A B X D b c h))
    (@one_cat_native_snake_kernel_second K C (@additive_preadditive C Prod t Add) C1 t
    (@additive_terminal_object C Prod t Add) T0 P Q A B X D b c h)))
    (@one_cat_native_snake_first_exact_comparison K C C1 Prod t Add T0 P Q N A B X D b c h)))))
≔ (@one_cat_native_snake_first_cover_reflect_path K C C1 Prod t Add T0 P Q N A B X D b c h
  (@cokernel_adjunction_family_func K C (@additive_preadditive C Prod t Add) t T0 Q (@transf_arrow_diagram_func
  K C (@comp_cat_fapp0 K (Functor_cat WalkingArrow_cat C) C (@adjunction_image_func C (@additive_preadditive C
  Prod t Add) t (@additive_terminal_object C Prod t Add) T0 P Q) (@zero_arrow_family_incoming_func K C t
  (@additive_terminal_object C Prod t Add) (@kernel_adjunction_family_func K C (@additive_preadditive C Prod t
  Add) t (@additive_terminal_object C Prod t Add) P (@one_cat_native_snake_alpha_diagram K C
  (@additive_preadditive C Prod t Add) C1 t (@additive_terminal_object C Prod t Add) T0 P A B X D b c h))
  (@transf_arrow_diagram_func K C (@kernel_adjunction_family_func K C (@additive_preadditive C Prod t Add) t
  (@additive_terminal_object C Prod t Add) P (@transf_arrow_diagram_func K C B X b))
  (@kernel_adjunction_family_func K C (@additive_preadditive C Prod t Add) t (@additive_terminal_object C Prod t
  Add) P (@one_cat_native_snake_gamma_diagram K C (@additive_preadditive C Prod t Add) C1 t
  (@additive_terminal_object C Prod t Add) T0 Q A B X D b c h)) (@one_cat_native_snake_kernel_second K C
  (@additive_preadditive C Prod t Add) C1 t (@additive_terminal_object C Prod t Add) T0 P Q A B X D b c h))
  (@one_cat_native_snake_first_exact_input K C C1 Prod t Add T0 P Q N A B X D b c h)))
  (@kernel_adjunction_family_func K C (@additive_preadditive C Prod t Add) t (@additive_terminal_object C Prod t
  Add) P (@transf_arrow_diagram_func K C (@kernel_adjunction_family_func K C (@additive_preadditive C Prod t
  Add) t (@additive_terminal_object C Prod t Add) P (@transf_arrow_diagram_func K C B X b))
  (@kernel_adjunction_family_func K C (@additive_preadditive C Prod t Add) t (@additive_terminal_object C Prod t
  Add) P (@one_cat_native_snake_gamma_diagram K C (@additive_preadditive C Prod t Add) C1 t
  (@additive_terminal_object C Prod t Add) T0 Q A B X D b c h)) (@one_cat_native_snake_kernel_second K C
  (@additive_preadditive C Prod t Add) C1 t (@additive_terminal_object C Prod t Add) T0 P Q A B X D b c h)))
  (@one_cat_native_snake_first_exact_comparison K C C1 Prod t Add T0 P Q N A B X D b c h))) (@comp_fapp0
  (Functor_cat K C) (@kernel_adjunction_family_func K C (@additive_preadditive C Prod t Add) t
  (@additive_terminal_object C Prod t Add) P (@transf_arrow_diagram_func K C (@one_cat_native_snake_image_func K
  C (@additive_preadditive C Prod t Add) C1 t (@additive_terminal_object C Prod t Add) T0 P Q A B X D b c h)
  (@kernel_adjunction_family_func K C (@additive_preadditive C Prod t Add) t (@additive_terminal_object C Prod t
  Add) P (@transf_arrow_diagram_func K C X D c)) (@one_cat_native_snake_image_lift K C (@additive_preadditive C
  Prod t Add) C1 t (@additive_terminal_object C Prod t Add) T0 P Q A B X D b c h)))
  (@kernel_adjunction_family_func K C (@additive_preadditive C Prod t Add) t (@additive_terminal_object C Prod t
  Add) P (@transf_arrow_diagram_func K C (@kernel_adjunction_family_func K C (@additive_preadditive C Prod t
  Add) t (@additive_terminal_object C Prod t Add) P (@transf_arrow_diagram_func K C B X b))
  (@kernel_adjunction_family_func K C (@additive_preadditive C Prod t Add) t (@additive_terminal_object C Prod t
  Add) P (@one_cat_native_snake_gamma_diagram K C (@additive_preadditive C Prod t Add) C1 t
  (@additive_terminal_object C Prod t Add) T0 Q A B X D b c h)) (@one_cat_native_snake_kernel_second K C
  (@additive_preadditive C Prod t Add) C1 t (@additive_terminal_object C Prod t Add) T0 P Q A B X D b c h)))
  (@cokernel_adjunction_family_func K C (@additive_preadditive C Prod t Add) t T0 Q (@transf_arrow_diagram_func
  K C (@comp_cat_fapp0 K (Functor_cat WalkingArrow_cat C) C (@adjunction_image_func C (@additive_preadditive C
  Prod t Add) t (@additive_terminal_object C Prod t Add) T0 P Q) (@zero_arrow_family_incoming_func K C t
  (@additive_terminal_object C Prod t Add) (@kernel_adjunction_family_func K C (@additive_preadditive C Prod t
  Add) t (@additive_terminal_object C Prod t Add) P (@one_cat_native_snake_alpha_diagram K C
  (@additive_preadditive C Prod t Add) C1 t (@additive_terminal_object C Prod t Add) T0 P A B X D b c h))
  (@transf_arrow_diagram_func K C (@kernel_adjunction_family_func K C (@additive_preadditive C Prod t Add) t
  (@additive_terminal_object C Prod t Add) P (@transf_arrow_diagram_func K C B X b))
  (@kernel_adjunction_family_func K C (@additive_preadditive C Prod t Add) t (@additive_terminal_object C Prod t
  Add) P (@one_cat_native_snake_gamma_diagram K C (@additive_preadditive C Prod t Add) C1 t
  (@additive_terminal_object C Prod t Add) T0 Q A B X D b c h)) (@one_cat_native_snake_kernel_second K C
  (@additive_preadditive C Prod t Add) C1 t (@additive_terminal_object C Prod t Add) T0 P Q A B X D b c h))
  (@one_cat_native_snake_first_exact_input K C C1 Prod t Add T0 P Q N A B X D b c h)))
  (@kernel_adjunction_family_func K C (@additive_preadditive C Prod t Add) t (@additive_terminal_object C Prod t
  Add) P (@transf_arrow_diagram_func K C (@kernel_adjunction_family_func K C (@additive_preadditive C Prod t
  Add) t (@additive_terminal_object C Prod t Add) P (@transf_arrow_diagram_func K C B X b))
  (@kernel_adjunction_family_func K C (@additive_preadditive C Prod t Add) t (@additive_terminal_object C Prod t
  Add) P (@one_cat_native_snake_gamma_diagram K C (@additive_preadditive C Prod t Add) C1 t
  (@additive_terminal_object C Prod t Add) T0 Q A B X D b c h)) (@one_cat_native_snake_kernel_second K C
  (@additive_preadditive C Prod t Add) C1 t (@additive_terminal_object C Prod t Add) T0 P Q A B X D b c h)))
  (@one_cat_native_snake_first_exact_comparison K C C1 Prod t Add T0 P Q N A B X D b c h)))
  (@cokernel_adjunction_family_projection_transf K C (@additive_preadditive C Prod t Add) t T0 Q
  (@transf_arrow_diagram_func K C (@comp_cat_fapp0 K (Functor_cat WalkingArrow_cat C) C (@adjunction_image_func
  C (@additive_preadditive C Prod t Add) t (@additive_terminal_object C Prod t Add) T0 P Q)
  (@zero_arrow_family_incoming_func K C t (@additive_terminal_object C Prod t Add)
  (@kernel_adjunction_family_func K C (@additive_preadditive C Prod t Add) t (@additive_terminal_object C Prod t
  Add) P (@one_cat_native_snake_alpha_diagram K C (@additive_preadditive C Prod t Add) C1 t
  (@additive_terminal_object C Prod t Add) T0 P A B X D b c h)) (@transf_arrow_diagram_func K C
  (@kernel_adjunction_family_func K C (@additive_preadditive C Prod t Add) t (@additive_terminal_object C Prod t
  Add) P (@transf_arrow_diagram_func K C B X b)) (@kernel_adjunction_family_func K C (@additive_preadditive C
  Prod t Add) t (@additive_terminal_object C Prod t Add) P (@one_cat_native_snake_gamma_diagram K C
  (@additive_preadditive C Prod t Add) C1 t (@additive_terminal_object C Prod t Add) T0 Q A B X D b c h))
  (@one_cat_native_snake_kernel_second K C (@additive_preadditive C Prod t Add) C1 t (@additive_terminal_object
  C Prod t Add) T0 P Q A B X D b c h)) (@one_cat_native_snake_first_exact_input K C C1 Prod t Add T0 P Q N A B X
  D b c h))) (@kernel_adjunction_family_func K C (@additive_preadditive C Prod t Add) t
  (@additive_terminal_object C Prod t Add) P (@transf_arrow_diagram_func K C (@kernel_adjunction_family_func K C
  (@additive_preadditive C Prod t Add) t (@additive_terminal_object C Prod t Add) P (@transf_arrow_diagram_func
  K C B X b)) (@kernel_adjunction_family_func K C (@additive_preadditive C Prod t Add) t
  (@additive_terminal_object C Prod t Add) P (@one_cat_native_snake_gamma_diagram K C (@additive_preadditive C
  Prod t Add) C1 t (@additive_terminal_object C Prod t Add) T0 Q A B X D b c h))
  (@one_cat_native_snake_kernel_second K C (@additive_preadditive C Prod t Add) C1 t (@additive_terminal_object
  C Prod t Add) T0 P Q A B X D b c h))) (@one_cat_native_snake_first_exact_comparison K C C1 Prod t Add T0 P Q N
  A B X D b c h))) (@one_cat_native_snake_first_image_kernel_to_kernel K C (@additive_preadditive C Prod t Add)
  C1 t (@additive_terminal_object C Prod t Add) T0 P Q A B X D b c h)) (@zero_arrow_family_zero_transf K C t
  (@additive_terminal_object C Prod t Add) T0 (@kernel_adjunction_family_func K C (@additive_preadditive C Prod
  t Add) t (@additive_terminal_object C Prod t Add) P (@transf_arrow_diagram_func K C
  (@one_cat_native_snake_image_func K C (@additive_preadditive C Prod t Add) C1 t (@additive_terminal_object C
  Prod t Add) T0 P Q A B X D b c h) (@kernel_adjunction_family_func K C (@additive_preadditive C Prod t Add) t
  (@additive_terminal_object C Prod t Add) P (@transf_arrow_diagram_func K C X D c))
  (@one_cat_native_snake_image_lift K C (@additive_preadditive C Prod t Add) C1 t (@additive_terminal_object C
  Prod t Add) T0 P Q A B X D b c h))) (@cokernel_adjunction_family_func K C (@additive_preadditive C Prod t Add)
  t T0 Q (@transf_arrow_diagram_func K C (@comp_cat_fapp0 K (Functor_cat WalkingArrow_cat C) C
  (@adjunction_image_func C (@additive_preadditive C Prod t Add) t (@additive_terminal_object C Prod t Add) T0 P
  Q) (@zero_arrow_family_incoming_func K C t (@additive_terminal_object C Prod t Add)
  (@kernel_adjunction_family_func K C (@additive_preadditive C Prod t Add) t (@additive_terminal_object C Prod t
  Add) P (@one_cat_native_snake_alpha_diagram K C (@additive_preadditive C Prod t Add) C1 t
  (@additive_terminal_object C Prod t Add) T0 P A B X D b c h)) (@transf_arrow_diagram_func K C
  (@kernel_adjunction_family_func K C (@additive_preadditive C Prod t Add) t (@additive_terminal_object C Prod t
  Add) P (@transf_arrow_diagram_func K C B X b)) (@kernel_adjunction_family_func K C (@additive_preadditive C
  Prod t Add) t (@additive_terminal_object C Prod t Add) P (@one_cat_native_snake_gamma_diagram K C
  (@additive_preadditive C Prod t Add) C1 t (@additive_terminal_object C Prod t Add) T0 Q A B X D b c h))
  (@one_cat_native_snake_kernel_second K C (@additive_preadditive C Prod t Add) C1 t (@additive_terminal_object
  C Prod t Add) T0 P Q A B X D b c h)) (@one_cat_native_snake_first_exact_input K C C1 Prod t Add T0 P Q N A B X
  D b c h))) (@kernel_adjunction_family_func K C (@additive_preadditive C Prod t Add) t
  (@additive_terminal_object C Prod t Add) P (@transf_arrow_diagram_func K C (@kernel_adjunction_family_func K C
  (@additive_preadditive C Prod t Add) t (@additive_terminal_object C Prod t Add) P (@transf_arrow_diagram_func
  K C B X b)) (@kernel_adjunction_family_func K C (@additive_preadditive C Prod t Add) t
  (@additive_terminal_object C Prod t Add) P (@one_cat_native_snake_gamma_diagram K C (@additive_preadditive C
  Prod t Add) C1 t (@additive_terminal_object C Prod t Add) T0 Q A B X D b c h))
  (@one_cat_native_snake_kernel_second K C (@additive_preadditive C Prod t Add) C1 t (@additive_terminal_object
  C Prod t Add) T0 P Q A B X D b c h))) (@one_cat_native_snake_first_exact_comparison K C C1 Prod t Add T0 P Q N
  A B X D b c h)))) (@eq_trans _ _ _ _ (@eq_sym _ _ _ (@comp_assoc (Functor_cat K C)
  (@one_cat_native_snake_first_cover_source K C (@additive_preadditive C Prod t Add) C1 t
  (@additive_terminal_object C Prod t Add) T0 P Q A B X D b c h) (@kernel_adjunction_family_func K C
  (@additive_preadditive C Prod t Add) t (@additive_terminal_object C Prod t Add) P (@transf_arrow_diagram_func
  K C (@one_cat_native_snake_image_func K C (@additive_preadditive C Prod t Add) C1 t (@additive_terminal_object
  C Prod t Add) T0 P Q A B X D b c h) (@kernel_adjunction_family_func K C (@additive_preadditive C Prod t Add) t
  (@additive_terminal_object C Prod t Add) P (@transf_arrow_diagram_func K C X D c))
  (@one_cat_native_snake_image_lift K C (@additive_preadditive C Prod t Add) C1 t (@additive_terminal_object C
  Prod t Add) T0 P Q A B X D b c h))) (@kernel_adjunction_family_func K C (@additive_preadditive C Prod t Add) t
  (@additive_terminal_object C Prod t Add) P (@transf_arrow_diagram_func K C (@kernel_adjunction_family_func K C
  (@additive_preadditive C Prod t Add) t (@additive_terminal_object C Prod t Add) P (@transf_arrow_diagram_func
  K C B X b)) (@kernel_adjunction_family_func K C (@additive_preadditive C Prod t Add) t
  (@additive_terminal_object C Prod t Add) P (@one_cat_native_snake_gamma_diagram K C (@additive_preadditive C
  Prod t Add) C1 t (@additive_terminal_object C Prod t Add) T0 Q A B X D b c h))
  (@one_cat_native_snake_kernel_second K C (@additive_preadditive C Prod t Add) C1 t (@additive_terminal_object
  C Prod t Add) T0 P Q A B X D b c h))) (@cokernel_adjunction_family_func K C (@additive_preadditive C Prod t
  Add) t T0 Q (@transf_arrow_diagram_func K C (@comp_cat_fapp0 K (Functor_cat WalkingArrow_cat C) C
  (@adjunction_image_func C (@additive_preadditive C Prod t Add) t (@additive_terminal_object C Prod t Add) T0 P
  Q) (@zero_arrow_family_incoming_func K C t (@additive_terminal_object C Prod t Add)
  (@kernel_adjunction_family_func K C (@additive_preadditive C Prod t Add) t (@additive_terminal_object C Prod t
  Add) P (@one_cat_native_snake_alpha_diagram K C (@additive_preadditive C Prod t Add) C1 t
  (@additive_terminal_object C Prod t Add) T0 P A B X D b c h)) (@transf_arrow_diagram_func K C
  (@kernel_adjunction_family_func K C (@additive_preadditive C Prod t Add) t (@additive_terminal_object C Prod t
  Add) P (@transf_arrow_diagram_func K C B X b)) (@kernel_adjunction_family_func K C (@additive_preadditive C
  Prod t Add) t (@additive_terminal_object C Prod t Add) P (@one_cat_native_snake_gamma_diagram K C
  (@additive_preadditive C Prod t Add) C1 t (@additive_terminal_object C Prod t Add) T0 Q A B X D b c h))
  (@one_cat_native_snake_kernel_second K C (@additive_preadditive C Prod t Add) C1 t (@additive_terminal_object
  C Prod t Add) T0 P Q A B X D b c h)) (@one_cat_native_snake_first_exact_input K C C1 Prod t Add T0 P Q N A B X
  D b c h))) (@kernel_adjunction_family_func K C (@additive_preadditive C Prod t Add) t
  (@additive_terminal_object C Prod t Add) P (@transf_arrow_diagram_func K C (@kernel_adjunction_family_func K C
  (@additive_preadditive C Prod t Add) t (@additive_terminal_object C Prod t Add) P (@transf_arrow_diagram_func
  K C B X b)) (@kernel_adjunction_family_func K C (@additive_preadditive C Prod t Add) t
  (@additive_terminal_object C Prod t Add) P (@one_cat_native_snake_gamma_diagram K C (@additive_preadditive C
  Prod t Add) C1 t (@additive_terminal_object C Prod t Add) T0 Q A B X D b c h))
  (@one_cat_native_snake_kernel_second K C (@additive_preadditive C Prod t Add) C1 t (@additive_terminal_object
  C Prod t Add) T0 P Q A B X D b c h))) (@one_cat_native_snake_first_exact_comparison K C C1 Prod t Add T0 P Q N
  A B X D b c h))) (@cokernel_adjunction_family_projection_transf K C (@additive_preadditive C Prod t Add) t T0
  Q (@transf_arrow_diagram_func K C (@comp_cat_fapp0 K (Functor_cat WalkingArrow_cat C) C
  (@adjunction_image_func C (@additive_preadditive C Prod t Add) t (@additive_terminal_object C Prod t Add) T0 P
  Q) (@zero_arrow_family_incoming_func K C t (@additive_terminal_object C Prod t Add)
  (@kernel_adjunction_family_func K C (@additive_preadditive C Prod t Add) t (@additive_terminal_object C Prod t
  Add) P (@one_cat_native_snake_alpha_diagram K C (@additive_preadditive C Prod t Add) C1 t
  (@additive_terminal_object C Prod t Add) T0 P A B X D b c h)) (@transf_arrow_diagram_func K C
  (@kernel_adjunction_family_func K C (@additive_preadditive C Prod t Add) t (@additive_terminal_object C Prod t
  Add) P (@transf_arrow_diagram_func K C B X b)) (@kernel_adjunction_family_func K C (@additive_preadditive C
  Prod t Add) t (@additive_terminal_object C Prod t Add) P (@one_cat_native_snake_gamma_diagram K C
  (@additive_preadditive C Prod t Add) C1 t (@additive_terminal_object C Prod t Add) T0 Q A B X D b c h))
  (@one_cat_native_snake_kernel_second K C (@additive_preadditive C Prod t Add) C1 t (@additive_terminal_object
  C Prod t Add) T0 P Q A B X D b c h)) (@one_cat_native_snake_first_exact_input K C C1 Prod t Add T0 P Q N A B X
  D b c h))) (@kernel_adjunction_family_func K C (@additive_preadditive C Prod t Add) t
  (@additive_terminal_object C Prod t Add) P (@transf_arrow_diagram_func K C (@kernel_adjunction_family_func K C
  (@additive_preadditive C Prod t Add) t (@additive_terminal_object C Prod t Add) P (@transf_arrow_diagram_func
  K C B X b)) (@kernel_adjunction_family_func K C (@additive_preadditive C Prod t Add) t
  (@additive_terminal_object C Prod t Add) P (@one_cat_native_snake_gamma_diagram K C (@additive_preadditive C
  Prod t Add) C1 t (@additive_terminal_object C Prod t Add) T0 Q A B X D b c h))
  (@one_cat_native_snake_kernel_second K C (@additive_preadditive C Prod t Add) C1 t (@additive_terminal_object
  C Prod t Add) T0 P Q A B X D b c h))) (@one_cat_native_snake_first_exact_comparison K C C1 Prod t Add T0 P Q N
  A B X D b c h))) (@one_cat_native_snake_first_image_kernel_to_kernel K C (@additive_preadditive C Prod t Add)
  C1 t (@additive_terminal_object C Prod t Add) T0 P Q A B X D b c h) (@one_cat_native_snake_first_cover_transf
  K C (@additive_preadditive C Prod t Add) C1 t (@additive_terminal_object C Prod t Add) T0 P Q A B X D b c h)))
  (@eq_trans _ _ _ _ (@eq_ap (@Transf K C (@one_cat_native_snake_first_cover_source K C (@additive_preadditive C
  Prod t Add) C1 t (@additive_terminal_object C Prod t Add) T0 P Q A B X D b c h)
  (@kernel_adjunction_family_func K C (@additive_preadditive C Prod t Add) t (@additive_terminal_object C Prod t
  Add) P (@transf_arrow_diagram_func K C (@kernel_adjunction_family_func K C (@additive_preadditive C Prod t
  Add) t (@additive_terminal_object C Prod t Add) P (@transf_arrow_diagram_func K C B X b))
  (@kernel_adjunction_family_func K C (@additive_preadditive C Prod t Add) t (@additive_terminal_object C Prod t
  Add) P (@one_cat_native_snake_gamma_diagram K C (@additive_preadditive C Prod t Add) C1 t
  (@additive_terminal_object C Prod t Add) T0 Q A B X D b c h)) (@one_cat_native_snake_kernel_second K C
  (@additive_preadditive C Prod t Add) C1 t (@additive_terminal_object C Prod t Add) T0 P Q A B X D b c h))))
  (@Transf K C (@one_cat_native_snake_first_cover_source K C (@additive_preadditive C Prod t Add) C1 t
  (@additive_terminal_object C Prod t Add) T0 P Q A B X D b c h) (@cokernel_adjunction_family_func K C
  (@additive_preadditive C Prod t Add) t T0 Q (@transf_arrow_diagram_func K C (@comp_cat_fapp0 K (Functor_cat
  WalkingArrow_cat C) C (@adjunction_image_func C (@additive_preadditive C Prod t Add) t
  (@additive_terminal_object C Prod t Add) T0 P Q) (@zero_arrow_family_incoming_func K C t
  (@additive_terminal_object C Prod t Add) (@kernel_adjunction_family_func K C (@additive_preadditive C Prod t
  Add) t (@additive_terminal_object C Prod t Add) P (@one_cat_native_snake_alpha_diagram K C
  (@additive_preadditive C Prod t Add) C1 t (@additive_terminal_object C Prod t Add) T0 P A B X D b c h))
  (@transf_arrow_diagram_func K C (@kernel_adjunction_family_func K C (@additive_preadditive C Prod t Add) t
  (@additive_terminal_object C Prod t Add) P (@transf_arrow_diagram_func K C B X b))
  (@kernel_adjunction_family_func K C (@additive_preadditive C Prod t Add) t (@additive_terminal_object C Prod t
  Add) P (@one_cat_native_snake_gamma_diagram K C (@additive_preadditive C Prod t Add) C1 t
  (@additive_terminal_object C Prod t Add) T0 Q A B X D b c h)) (@one_cat_native_snake_kernel_second K C
  (@additive_preadditive C Prod t Add) C1 t (@additive_terminal_object C Prod t Add) T0 P Q A B X D b c h))
  (@one_cat_native_snake_first_exact_input K C C1 Prod t Add T0 P Q N A B X D b c h)))
  (@kernel_adjunction_family_func K C (@additive_preadditive C Prod t Add) t (@additive_terminal_object C Prod t
  Add) P (@transf_arrow_diagram_func K C (@kernel_adjunction_family_func K C (@additive_preadditive C Prod t
  Add) t (@additive_terminal_object C Prod t Add) P (@transf_arrow_diagram_func K C B X b))
  (@kernel_adjunction_family_func K C (@additive_preadditive C Prod t Add) t (@additive_terminal_object C Prod t
  Add) P (@one_cat_native_snake_gamma_diagram K C (@additive_preadditive C Prod t Add) C1 t
  (@additive_terminal_object C Prod t Add) T0 Q A B X D b c h)) (@one_cat_native_snake_kernel_second K C
  (@additive_preadditive C Prod t Add) C1 t (@additive_terminal_object C Prod t Add) T0 P Q A B X D b c h)))
  (@one_cat_native_snake_first_exact_comparison K C C1 Prod t Add T0 P Q N A B X D b c h)))) (λ v : τ (@Transf K
  C (@one_cat_native_snake_first_cover_source K C (@additive_preadditive C Prod t Add) C1 t
  (@additive_terminal_object C Prod t Add) T0 P Q A B X D b c h) (@kernel_adjunction_family_func K C
  (@additive_preadditive C Prod t Add) t (@additive_terminal_object C Prod t Add) P (@transf_arrow_diagram_func
  K C (@kernel_adjunction_family_func K C (@additive_preadditive C Prod t Add) t (@additive_terminal_object C
  Prod t Add) P (@transf_arrow_diagram_func K C B X b)) (@kernel_adjunction_family_func K C
  (@additive_preadditive C Prod t Add) t (@additive_terminal_object C Prod t Add) P
  (@one_cat_native_snake_gamma_diagram K C (@additive_preadditive C Prod t Add) C1 t (@additive_terminal_object
  C Prod t Add) T0 Q A B X D b c h)) (@one_cat_native_snake_kernel_second K C (@additive_preadditive C Prod t
  Add) C1 t (@additive_terminal_object C Prod t Add) T0 P Q A B X D b c h)))), (@comp_fapp0 (Functor_cat K C)
  (@one_cat_native_snake_first_cover_source K C (@additive_preadditive C Prod t Add) C1 t
  (@additive_terminal_object C Prod t Add) T0 P Q A B X D b c h) (@kernel_adjunction_family_func K C
  (@additive_preadditive C Prod t Add) t (@additive_terminal_object C Prod t Add) P (@transf_arrow_diagram_func
  K C (@kernel_adjunction_family_func K C (@additive_preadditive C Prod t Add) t (@additive_terminal_object C
  Prod t Add) P (@transf_arrow_diagram_func K C B X b)) (@kernel_adjunction_family_func K C
  (@additive_preadditive C Prod t Add) t (@additive_terminal_object C Prod t Add) P
  (@one_cat_native_snake_gamma_diagram K C (@additive_preadditive C Prod t Add) C1 t (@additive_terminal_object
  C Prod t Add) T0 Q A B X D b c h)) (@one_cat_native_snake_kernel_second K C (@additive_preadditive C Prod t
  Add) C1 t (@additive_terminal_object C Prod t Add) T0 P Q A B X D b c h))) (@cokernel_adjunction_family_func K
  C (@additive_preadditive C Prod t Add) t T0 Q (@transf_arrow_diagram_func K C (@comp_cat_fapp0 K (Functor_cat
  WalkingArrow_cat C) C (@adjunction_image_func C (@additive_preadditive C Prod t Add) t
  (@additive_terminal_object C Prod t Add) T0 P Q) (@zero_arrow_family_incoming_func K C t
  (@additive_terminal_object C Prod t Add) (@kernel_adjunction_family_func K C (@additive_preadditive C Prod t
  Add) t (@additive_terminal_object C Prod t Add) P (@one_cat_native_snake_alpha_diagram K C
  (@additive_preadditive C Prod t Add) C1 t (@additive_terminal_object C Prod t Add) T0 P A B X D b c h))
  (@transf_arrow_diagram_func K C (@kernel_adjunction_family_func K C (@additive_preadditive C Prod t Add) t
  (@additive_terminal_object C Prod t Add) P (@transf_arrow_diagram_func K C B X b))
  (@kernel_adjunction_family_func K C (@additive_preadditive C Prod t Add) t (@additive_terminal_object C Prod t
  Add) P (@one_cat_native_snake_gamma_diagram K C (@additive_preadditive C Prod t Add) C1 t
  (@additive_terminal_object C Prod t Add) T0 Q A B X D b c h)) (@one_cat_native_snake_kernel_second K C
  (@additive_preadditive C Prod t Add) C1 t (@additive_terminal_object C Prod t Add) T0 P Q A B X D b c h))
  (@one_cat_native_snake_first_exact_input K C C1 Prod t Add T0 P Q N A B X D b c h)))
  (@kernel_adjunction_family_func K C (@additive_preadditive C Prod t Add) t (@additive_terminal_object C Prod t
  Add) P (@transf_arrow_diagram_func K C (@kernel_adjunction_family_func K C (@additive_preadditive C Prod t
  Add) t (@additive_terminal_object C Prod t Add) P (@transf_arrow_diagram_func K C B X b))
  (@kernel_adjunction_family_func K C (@additive_preadditive C Prod t Add) t (@additive_terminal_object C Prod t
  Add) P (@one_cat_native_snake_gamma_diagram K C (@additive_preadditive C Prod t Add) C1 t
  (@additive_terminal_object C Prod t Add) T0 Q A B X D b c h)) (@one_cat_native_snake_kernel_second K C
  (@additive_preadditive C Prod t Add) C1 t (@additive_terminal_object C Prod t Add) T0 P Q A B X D b c h)))
  (@one_cat_native_snake_first_exact_comparison K C C1 Prod t Add T0 P Q N A B X D b c h)))
  (@cokernel_adjunction_family_projection_transf K C (@additive_preadditive C Prod t Add) t T0 Q
  (@transf_arrow_diagram_func K C (@comp_cat_fapp0 K (Functor_cat WalkingArrow_cat C) C (@adjunction_image_func
  C (@additive_preadditive C Prod t Add) t (@additive_terminal_object C Prod t Add) T0 P Q)
  (@zero_arrow_family_incoming_func K C t (@additive_terminal_object C Prod t Add)
  (@kernel_adjunction_family_func K C (@additive_preadditive C Prod t Add) t (@additive_terminal_object C Prod t
  Add) P (@one_cat_native_snake_alpha_diagram K C (@additive_preadditive C Prod t Add) C1 t
  (@additive_terminal_object C Prod t Add) T0 P A B X D b c h)) (@transf_arrow_diagram_func K C
  (@kernel_adjunction_family_func K C (@additive_preadditive C Prod t Add) t (@additive_terminal_object C Prod t
  Add) P (@transf_arrow_diagram_func K C B X b)) (@kernel_adjunction_family_func K C (@additive_preadditive C
  Prod t Add) t (@additive_terminal_object C Prod t Add) P (@one_cat_native_snake_gamma_diagram K C
  (@additive_preadditive C Prod t Add) C1 t (@additive_terminal_object C Prod t Add) T0 Q A B X D b c h))
  (@one_cat_native_snake_kernel_second K C (@additive_preadditive C Prod t Add) C1 t (@additive_terminal_object
  C Prod t Add) T0 P Q A B X D b c h)) (@one_cat_native_snake_first_exact_input K C C1 Prod t Add T0 P Q N A B X
  D b c h))) (@kernel_adjunction_family_func K C (@additive_preadditive C Prod t Add) t
  (@additive_terminal_object C Prod t Add) P (@transf_arrow_diagram_func K C (@kernel_adjunction_family_func K C
  (@additive_preadditive C Prod t Add) t (@additive_terminal_object C Prod t Add) P (@transf_arrow_diagram_func
  K C B X b)) (@kernel_adjunction_family_func K C (@additive_preadditive C Prod t Add) t
  (@additive_terminal_object C Prod t Add) P (@one_cat_native_snake_gamma_diagram K C (@additive_preadditive C
  Prod t Add) C1 t (@additive_terminal_object C Prod t Add) T0 Q A B X D b c h))
  (@one_cat_native_snake_kernel_second K C (@additive_preadditive C Prod t Add) C1 t (@additive_terminal_object
  C Prod t Add) T0 P Q A B X D b c h))) (@one_cat_native_snake_first_exact_comparison K C C1 Prod t Add T0 P Q N
  A B X D b c h))) v)) _ _ (@eq_sym _ _ _ (@one_cat_native_snake_first_comparison_covers_path K C C1 Prod t Add
  T0 P Q N A B X D b c h))) (@eq_trans _ _ _ _ (@comp_assoc (Functor_cat K C)
  (@one_cat_native_snake_first_cover_source K C (@additive_preadditive C Prod t Add) C1 t
  (@additive_terminal_object C Prod t Add) T0 P Q A B X D b c h) (@comp_cat_fapp0 K (Functor_cat
  WalkingArrow_cat C) C (@adjunction_image_func C (@additive_preadditive C Prod t Add) t
  (@additive_terminal_object C Prod t Add) T0 P Q) (@zero_arrow_family_incoming_func K C t
  (@additive_terminal_object C Prod t Add) (@kernel_adjunction_family_func K C (@additive_preadditive C Prod t
  Add) t (@additive_terminal_object C Prod t Add) P (@one_cat_native_snake_alpha_diagram K C
  (@additive_preadditive C Prod t Add) C1 t (@additive_terminal_object C Prod t Add) T0 P A B X D b c h))
  (@transf_arrow_diagram_func K C (@kernel_adjunction_family_func K C (@additive_preadditive C Prod t Add) t
  (@additive_terminal_object C Prod t Add) P (@transf_arrow_diagram_func K C B X b))
  (@kernel_adjunction_family_func K C (@additive_preadditive C Prod t Add) t (@additive_terminal_object C Prod t
  Add) P (@one_cat_native_snake_gamma_diagram K C (@additive_preadditive C Prod t Add) C1 t
  (@additive_terminal_object C Prod t Add) T0 Q A B X D b c h)) (@one_cat_native_snake_kernel_second K C
  (@additive_preadditive C Prod t Add) C1 t (@additive_terminal_object C Prod t Add) T0 P Q A B X D b c h))
  (@one_cat_native_snake_first_exact_input K C C1 Prod t Add T0 P Q N A B X D b c h)))
  (@kernel_adjunction_family_func K C (@additive_preadditive C Prod t Add) t (@additive_terminal_object C Prod t
  Add) P (@transf_arrow_diagram_func K C (@kernel_adjunction_family_func K C (@additive_preadditive C Prod t
  Add) t (@additive_terminal_object C Prod t Add) P (@transf_arrow_diagram_func K C B X b))
  (@kernel_adjunction_family_func K C (@additive_preadditive C Prod t Add) t (@additive_terminal_object C Prod t
  Add) P (@one_cat_native_snake_gamma_diagram K C (@additive_preadditive C Prod t Add) C1 t
  (@additive_terminal_object C Prod t Add) T0 Q A B X D b c h)) (@one_cat_native_snake_kernel_second K C
  (@additive_preadditive C Prod t Add) C1 t (@additive_terminal_object C Prod t Add) T0 P Q A B X D b c h)))
  (@cokernel_adjunction_family_func K C (@additive_preadditive C Prod t Add) t T0 Q (@transf_arrow_diagram_func
  K C (@comp_cat_fapp0 K (Functor_cat WalkingArrow_cat C) C (@adjunction_image_func C (@additive_preadditive C
  Prod t Add) t (@additive_terminal_object C Prod t Add) T0 P Q) (@zero_arrow_family_incoming_func K C t
  (@additive_terminal_object C Prod t Add) (@kernel_adjunction_family_func K C (@additive_preadditive C Prod t
  Add) t (@additive_terminal_object C Prod t Add) P (@one_cat_native_snake_alpha_diagram K C
  (@additive_preadditive C Prod t Add) C1 t (@additive_terminal_object C Prod t Add) T0 P A B X D b c h))
  (@transf_arrow_diagram_func K C (@kernel_adjunction_family_func K C (@additive_preadditive C Prod t Add) t
  (@additive_terminal_object C Prod t Add) P (@transf_arrow_diagram_func K C B X b))
  (@kernel_adjunction_family_func K C (@additive_preadditive C Prod t Add) t (@additive_terminal_object C Prod t
  Add) P (@one_cat_native_snake_gamma_diagram K C (@additive_preadditive C Prod t Add) C1 t
  (@additive_terminal_object C Prod t Add) T0 Q A B X D b c h)) (@one_cat_native_snake_kernel_second K C
  (@additive_preadditive C Prod t Add) C1 t (@additive_terminal_object C Prod t Add) T0 P Q A B X D b c h))
  (@one_cat_native_snake_first_exact_input K C C1 Prod t Add T0 P Q N A B X D b c h)))
  (@kernel_adjunction_family_func K C (@additive_preadditive C Prod t Add) t (@additive_terminal_object C Prod t
  Add) P (@transf_arrow_diagram_func K C (@kernel_adjunction_family_func K C (@additive_preadditive C Prod t
  Add) t (@additive_terminal_object C Prod t Add) P (@transf_arrow_diagram_func K C B X b))
  (@kernel_adjunction_family_func K C (@additive_preadditive C Prod t Add) t (@additive_terminal_object C Prod t
  Add) P (@one_cat_native_snake_gamma_diagram K C (@additive_preadditive C Prod t Add) C1 t
  (@additive_terminal_object C Prod t Add) T0 Q A B X D b c h)) (@one_cat_native_snake_kernel_second K C
  (@additive_preadditive C Prod t Add) C1 t (@additive_terminal_object C Prod t Add) T0 P Q A B X D b c h)))
  (@one_cat_native_snake_first_exact_comparison K C C1 Prod t Add T0 P Q N A B X D b c h)))
  (@cokernel_adjunction_family_projection_transf K C (@additive_preadditive C Prod t Add) t T0 Q
  (@transf_arrow_diagram_func K C (@comp_cat_fapp0 K (Functor_cat WalkingArrow_cat C) C (@adjunction_image_func
  C (@additive_preadditive C Prod t Add) t (@additive_terminal_object C Prod t Add) T0 P Q)
  (@zero_arrow_family_incoming_func K C t (@additive_terminal_object C Prod t Add)
  (@kernel_adjunction_family_func K C (@additive_preadditive C Prod t Add) t (@additive_terminal_object C Prod t
  Add) P (@one_cat_native_snake_alpha_diagram K C (@additive_preadditive C Prod t Add) C1 t
  (@additive_terminal_object C Prod t Add) T0 P A B X D b c h)) (@transf_arrow_diagram_func K C
  (@kernel_adjunction_family_func K C (@additive_preadditive C Prod t Add) t (@additive_terminal_object C Prod t
  Add) P (@transf_arrow_diagram_func K C B X b)) (@kernel_adjunction_family_func K C (@additive_preadditive C
  Prod t Add) t (@additive_terminal_object C Prod t Add) P (@one_cat_native_snake_gamma_diagram K C
  (@additive_preadditive C Prod t Add) C1 t (@additive_terminal_object C Prod t Add) T0 Q A B X D b c h))
  (@one_cat_native_snake_kernel_second K C (@additive_preadditive C Prod t Add) C1 t (@additive_terminal_object
  C Prod t Add) T0 P Q A B X D b c h)) (@one_cat_native_snake_first_exact_input K C C1 Prod t Add T0 P Q N A B X
  D b c h))) (@kernel_adjunction_family_func K C (@additive_preadditive C Prod t Add) t
  (@additive_terminal_object C Prod t Add) P (@transf_arrow_diagram_func K C (@kernel_adjunction_family_func K C
  (@additive_preadditive C Prod t Add) t (@additive_terminal_object C Prod t Add) P (@transf_arrow_diagram_func
  K C B X b)) (@kernel_adjunction_family_func K C (@additive_preadditive C Prod t Add) t
  (@additive_terminal_object C Prod t Add) P (@one_cat_native_snake_gamma_diagram K C (@additive_preadditive C
  Prod t Add) C1 t (@additive_terminal_object C Prod t Add) T0 Q A B X D b c h))
  (@one_cat_native_snake_kernel_second K C (@additive_preadditive C Prod t Add) C1 t (@additive_terminal_object
  C Prod t Add) T0 P Q A B X D b c h))) (@one_cat_native_snake_first_exact_comparison K C C1 Prod t Add T0 P Q N
  A B X D b c h))) (@one_cat_native_snake_first_exact_comparison K C C1 Prod t Add T0 P Q N A B X D b c h)
  (@comp_fapp0 (Functor_cat K C) (@one_cat_native_snake_first_cover_source K C (@additive_preadditive C Prod t
  Add) C1 t (@additive_terminal_object C Prod t Add) T0 P Q A B X D b c h) (@kernel_adjunction_family_func K C
  (@additive_preadditive C Prod t Add) t (@additive_terminal_object C Prod t Add) P
  (@one_cat_native_snake_alpha_diagram K C (@additive_preadditive C Prod t Add) C1 t (@additive_terminal_object
  C Prod t Add) T0 P A B X D b c h)) (@comp_cat_fapp0 K (Functor_cat WalkingArrow_cat C) C
  (@adjunction_image_func C (@additive_preadditive C Prod t Add) t (@additive_terminal_object C Prod t Add) T0 P
  Q) (@zero_arrow_family_incoming_func K C t (@additive_terminal_object C Prod t Add)
  (@kernel_adjunction_family_func K C (@additive_preadditive C Prod t Add) t (@additive_terminal_object C Prod t
  Add) P (@one_cat_native_snake_alpha_diagram K C (@additive_preadditive C Prod t Add) C1 t
  (@additive_terminal_object C Prod t Add) T0 P A B X D b c h)) (@transf_arrow_diagram_func K C
  (@kernel_adjunction_family_func K C (@additive_preadditive C Prod t Add) t (@additive_terminal_object C Prod t
  Add) P (@transf_arrow_diagram_func K C B X b)) (@kernel_adjunction_family_func K C (@additive_preadditive C
  Prod t Add) t (@additive_terminal_object C Prod t Add) P (@one_cat_native_snake_gamma_diagram K C
  (@additive_preadditive C Prod t Add) C1 t (@additive_terminal_object C Prod t Add) T0 Q A B X D b c h))
  (@one_cat_native_snake_kernel_second K C (@additive_preadditive C Prod t Add) C1 t (@additive_terminal_object
  C Prod t Add) T0 P Q A B X D b c h)) (@one_cat_native_snake_first_exact_input K C C1 Prod t Add T0 P Q N A B X
  D b c h))) (@one_cat_image_family_source_transf K C (@additive_preadditive C Prod t Add) C1 t
  (@additive_terminal_object C Prod t Add) T0 P Q (@zero_arrow_family_incoming_func K C t
  (@additive_terminal_object C Prod t Add) (@kernel_adjunction_family_func K C (@additive_preadditive C Prod t
  Add) t (@additive_terminal_object C Prod t Add) P (@one_cat_native_snake_alpha_diagram K C
  (@additive_preadditive C Prod t Add) C1 t (@additive_terminal_object C Prod t Add) T0 P A B X D b c h))
  (@transf_arrow_diagram_func K C (@kernel_adjunction_family_func K C (@additive_preadditive C Prod t Add) t
  (@additive_terminal_object C Prod t Add) P (@transf_arrow_diagram_func K C B X b))
  (@kernel_adjunction_family_func K C (@additive_preadditive C Prod t Add) t (@additive_terminal_object C Prod t
  Add) P (@one_cat_native_snake_gamma_diagram K C (@additive_preadditive C Prod t Add) C1 t
  (@additive_terminal_object C Prod t Add) T0 Q A B X D b c h)) (@one_cat_native_snake_kernel_second K C
  (@additive_preadditive C Prod t Add) C1 t (@additive_terminal_object C Prod t Add) T0 P Q A B X D b c h))
  (@one_cat_native_snake_first_exact_input K C C1 Prod t Add T0 P Q N A B X D b c h)))
  (@one_cat_native_snake_first_cover_to_alpha_kernel K C (@additive_preadditive C Prod t Add) C1 t
  (@additive_terminal_object C Prod t Add) T0 P Q A B X D b c h))) (@eq_trans _ _ _ _ (@eq_ap (@Transf K C
  (@comp_cat_fapp0 K (Functor_cat WalkingArrow_cat C) C (@adjunction_image_func C (@additive_preadditive C Prod
  t Add) t (@additive_terminal_object C Prod t Add) T0 P Q) (@zero_arrow_family_incoming_func K C t
  (@additive_terminal_object C Prod t Add) (@kernel_adjunction_family_func K C (@additive_preadditive C Prod t
  Add) t (@additive_terminal_object C Prod t Add) P (@one_cat_native_snake_alpha_diagram K C
  (@additive_preadditive C Prod t Add) C1 t (@additive_terminal_object C Prod t Add) T0 P A B X D b c h))
  (@transf_arrow_diagram_func K C (@kernel_adjunction_family_func K C (@additive_preadditive C Prod t Add) t
  (@additive_terminal_object C Prod t Add) P (@transf_arrow_diagram_func K C B X b))
  (@kernel_adjunction_family_func K C (@additive_preadditive C Prod t Add) t (@additive_terminal_object C Prod t
  Add) P (@one_cat_native_snake_gamma_diagram K C (@additive_preadditive C Prod t Add) C1 t
  (@additive_terminal_object C Prod t Add) T0 Q A B X D b c h)) (@one_cat_native_snake_kernel_second K C
  (@additive_preadditive C Prod t Add) C1 t (@additive_terminal_object C Prod t Add) T0 P Q A B X D b c h))
  (@one_cat_native_snake_first_exact_input K C C1 Prod t Add T0 P Q N A B X D b c h)))
  (@cokernel_adjunction_family_func K C (@additive_preadditive C Prod t Add) t T0 Q (@transf_arrow_diagram_func
  K C (@comp_cat_fapp0 K (Functor_cat WalkingArrow_cat C) C (@adjunction_image_func C (@additive_preadditive C
  Prod t Add) t (@additive_terminal_object C Prod t Add) T0 P Q) (@zero_arrow_family_incoming_func K C t
  (@additive_terminal_object C Prod t Add) (@kernel_adjunction_family_func K C (@additive_preadditive C Prod t
  Add) t (@additive_terminal_object C Prod t Add) P (@one_cat_native_snake_alpha_diagram K C
  (@additive_preadditive C Prod t Add) C1 t (@additive_terminal_object C Prod t Add) T0 P A B X D b c h))
  (@transf_arrow_diagram_func K C (@kernel_adjunction_family_func K C (@additive_preadditive C Prod t Add) t
  (@additive_terminal_object C Prod t Add) P (@transf_arrow_diagram_func K C B X b))
  (@kernel_adjunction_family_func K C (@additive_preadditive C Prod t Add) t (@additive_terminal_object C Prod t
  Add) P (@one_cat_native_snake_gamma_diagram K C (@additive_preadditive C Prod t Add) C1 t
  (@additive_terminal_object C Prod t Add) T0 Q A B X D b c h)) (@one_cat_native_snake_kernel_second K C
  (@additive_preadditive C Prod t Add) C1 t (@additive_terminal_object C Prod t Add) T0 P Q A B X D b c h))
  (@one_cat_native_snake_first_exact_input K C C1 Prod t Add T0 P Q N A B X D b c h)))
  (@kernel_adjunction_family_func K C (@additive_preadditive C Prod t Add) t (@additive_terminal_object C Prod t
  Add) P (@transf_arrow_diagram_func K C (@kernel_adjunction_family_func K C (@additive_preadditive C Prod t
  Add) t (@additive_terminal_object C Prod t Add) P (@transf_arrow_diagram_func K C B X b))
  (@kernel_adjunction_family_func K C (@additive_preadditive C Prod t Add) t (@additive_terminal_object C Prod t
  Add) P (@one_cat_native_snake_gamma_diagram K C (@additive_preadditive C Prod t Add) C1 t
  (@additive_terminal_object C Prod t Add) T0 Q A B X D b c h)) (@one_cat_native_snake_kernel_second K C
  (@additive_preadditive C Prod t Add) C1 t (@additive_terminal_object C Prod t Add) T0 P Q A B X D b c h)))
  (@one_cat_native_snake_first_exact_comparison K C C1 Prod t Add T0 P Q N A B X D b c h)))) (@Transf K C
  (@one_cat_native_snake_first_cover_source K C (@additive_preadditive C Prod t Add) C1 t
  (@additive_terminal_object C Prod t Add) T0 P Q A B X D b c h) (@cokernel_adjunction_family_func K C
  (@additive_preadditive C Prod t Add) t T0 Q (@transf_arrow_diagram_func K C (@comp_cat_fapp0 K (Functor_cat
  WalkingArrow_cat C) C (@adjunction_image_func C (@additive_preadditive C Prod t Add) t
  (@additive_terminal_object C Prod t Add) T0 P Q) (@zero_arrow_family_incoming_func K C t
  (@additive_terminal_object C Prod t Add) (@kernel_adjunction_family_func K C (@additive_preadditive C Prod t
  Add) t (@additive_terminal_object C Prod t Add) P (@one_cat_native_snake_alpha_diagram K C
  (@additive_preadditive C Prod t Add) C1 t (@additive_terminal_object C Prod t Add) T0 P A B X D b c h))
  (@transf_arrow_diagram_func K C (@kernel_adjunction_family_func K C (@additive_preadditive C Prod t Add) t
  (@additive_terminal_object C Prod t Add) P (@transf_arrow_diagram_func K C B X b))
  (@kernel_adjunction_family_func K C (@additive_preadditive C Prod t Add) t (@additive_terminal_object C Prod t
  Add) P (@one_cat_native_snake_gamma_diagram K C (@additive_preadditive C Prod t Add) C1 t
  (@additive_terminal_object C Prod t Add) T0 Q A B X D b c h)) (@one_cat_native_snake_kernel_second K C
  (@additive_preadditive C Prod t Add) C1 t (@additive_terminal_object C Prod t Add) T0 P Q A B X D b c h))
  (@one_cat_native_snake_first_exact_input K C C1 Prod t Add T0 P Q N A B X D b c h)))
  (@kernel_adjunction_family_func K C (@additive_preadditive C Prod t Add) t (@additive_terminal_object C Prod t
  Add) P (@transf_arrow_diagram_func K C (@kernel_adjunction_family_func K C (@additive_preadditive C Prod t
  Add) t (@additive_terminal_object C Prod t Add) P (@transf_arrow_diagram_func K C B X b))
  (@kernel_adjunction_family_func K C (@additive_preadditive C Prod t Add) t (@additive_terminal_object C Prod t
  Add) P (@one_cat_native_snake_gamma_diagram K C (@additive_preadditive C Prod t Add) C1 t
  (@additive_terminal_object C Prod t Add) T0 Q A B X D b c h)) (@one_cat_native_snake_kernel_second K C
  (@additive_preadditive C Prod t Add) C1 t (@additive_terminal_object C Prod t Add) T0 P Q A B X D b c h)))
  (@one_cat_native_snake_first_exact_comparison K C C1 Prod t Add T0 P Q N A B X D b c h)))) (λ v : τ (@Transf K
  C (@comp_cat_fapp0 K (Functor_cat WalkingArrow_cat C) C (@adjunction_image_func C (@additive_preadditive C
  Prod t Add) t (@additive_terminal_object C Prod t Add) T0 P Q) (@zero_arrow_family_incoming_func K C t
  (@additive_terminal_object C Prod t Add) (@kernel_adjunction_family_func K C (@additive_preadditive C Prod t
  Add) t (@additive_terminal_object C Prod t Add) P (@one_cat_native_snake_alpha_diagram K C
  (@additive_preadditive C Prod t Add) C1 t (@additive_terminal_object C Prod t Add) T0 P A B X D b c h))
  (@transf_arrow_diagram_func K C (@kernel_adjunction_family_func K C (@additive_preadditive C Prod t Add) t
  (@additive_terminal_object C Prod t Add) P (@transf_arrow_diagram_func K C B X b))
  (@kernel_adjunction_family_func K C (@additive_preadditive C Prod t Add) t (@additive_terminal_object C Prod t
  Add) P (@one_cat_native_snake_gamma_diagram K C (@additive_preadditive C Prod t Add) C1 t
  (@additive_terminal_object C Prod t Add) T0 Q A B X D b c h)) (@one_cat_native_snake_kernel_second K C
  (@additive_preadditive C Prod t Add) C1 t (@additive_terminal_object C Prod t Add) T0 P Q A B X D b c h))
  (@one_cat_native_snake_first_exact_input K C C1 Prod t Add T0 P Q N A B X D b c h)))
  (@cokernel_adjunction_family_func K C (@additive_preadditive C Prod t Add) t T0 Q (@transf_arrow_diagram_func
  K C (@comp_cat_fapp0 K (Functor_cat WalkingArrow_cat C) C (@adjunction_image_func C (@additive_preadditive C
  Prod t Add) t (@additive_terminal_object C Prod t Add) T0 P Q) (@zero_arrow_family_incoming_func K C t
  (@additive_terminal_object C Prod t Add) (@kernel_adjunction_family_func K C (@additive_preadditive C Prod t
  Add) t (@additive_terminal_object C Prod t Add) P (@one_cat_native_snake_alpha_diagram K C
  (@additive_preadditive C Prod t Add) C1 t (@additive_terminal_object C Prod t Add) T0 P A B X D b c h))
  (@transf_arrow_diagram_func K C (@kernel_adjunction_family_func K C (@additive_preadditive C Prod t Add) t
  (@additive_terminal_object C Prod t Add) P (@transf_arrow_diagram_func K C B X b))
  (@kernel_adjunction_family_func K C (@additive_preadditive C Prod t Add) t (@additive_terminal_object C Prod t
  Add) P (@one_cat_native_snake_gamma_diagram K C (@additive_preadditive C Prod t Add) C1 t
  (@additive_terminal_object C Prod t Add) T0 Q A B X D b c h)) (@one_cat_native_snake_kernel_second K C
  (@additive_preadditive C Prod t Add) C1 t (@additive_terminal_object C Prod t Add) T0 P Q A B X D b c h))
  (@one_cat_native_snake_first_exact_input K C C1 Prod t Add T0 P Q N A B X D b c h)))
  (@kernel_adjunction_family_func K C (@additive_preadditive C Prod t Add) t (@additive_terminal_object C Prod t
  Add) P (@transf_arrow_diagram_func K C (@kernel_adjunction_family_func K C (@additive_preadditive C Prod t
  Add) t (@additive_terminal_object C Prod t Add) P (@transf_arrow_diagram_func K C B X b))
  (@kernel_adjunction_family_func K C (@additive_preadditive C Prod t Add) t (@additive_terminal_object C Prod t
  Add) P (@one_cat_native_snake_gamma_diagram K C (@additive_preadditive C Prod t Add) C1 t
  (@additive_terminal_object C Prod t Add) T0 Q A B X D b c h)) (@one_cat_native_snake_kernel_second K C
  (@additive_preadditive C Prod t Add) C1 t (@additive_terminal_object C Prod t Add) T0 P Q A B X D b c h)))
  (@one_cat_native_snake_first_exact_comparison K C C1 Prod t Add T0 P Q N A B X D b c h)))), (@comp_fapp0
  (Functor_cat K C) (@one_cat_native_snake_first_cover_source K C (@additive_preadditive C Prod t Add) C1 t
  (@additive_terminal_object C Prod t Add) T0 P Q A B X D b c h) (@comp_cat_fapp0 K (Functor_cat
  WalkingArrow_cat C) C (@adjunction_image_func C (@additive_preadditive C Prod t Add) t
  (@additive_terminal_object C Prod t Add) T0 P Q) (@zero_arrow_family_incoming_func K C t
  (@additive_terminal_object C Prod t Add) (@kernel_adjunction_family_func K C (@additive_preadditive C Prod t
  Add) t (@additive_terminal_object C Prod t Add) P (@one_cat_native_snake_alpha_diagram K C
  (@additive_preadditive C Prod t Add) C1 t (@additive_terminal_object C Prod t Add) T0 P A B X D b c h))
  (@transf_arrow_diagram_func K C (@kernel_adjunction_family_func K C (@additive_preadditive C Prod t Add) t
  (@additive_terminal_object C Prod t Add) P (@transf_arrow_diagram_func K C B X b))
  (@kernel_adjunction_family_func K C (@additive_preadditive C Prod t Add) t (@additive_terminal_object C Prod t
  Add) P (@one_cat_native_snake_gamma_diagram K C (@additive_preadditive C Prod t Add) C1 t
  (@additive_terminal_object C Prod t Add) T0 Q A B X D b c h)) (@one_cat_native_snake_kernel_second K C
  (@additive_preadditive C Prod t Add) C1 t (@additive_terminal_object C Prod t Add) T0 P Q A B X D b c h))
  (@one_cat_native_snake_first_exact_input K C C1 Prod t Add T0 P Q N A B X D b c h)))
  (@cokernel_adjunction_family_func K C (@additive_preadditive C Prod t Add) t T0 Q (@transf_arrow_diagram_func
  K C (@comp_cat_fapp0 K (Functor_cat WalkingArrow_cat C) C (@adjunction_image_func C (@additive_preadditive C
  Prod t Add) t (@additive_terminal_object C Prod t Add) T0 P Q) (@zero_arrow_family_incoming_func K C t
  (@additive_terminal_object C Prod t Add) (@kernel_adjunction_family_func K C (@additive_preadditive C Prod t
  Add) t (@additive_terminal_object C Prod t Add) P (@one_cat_native_snake_alpha_diagram K C
  (@additive_preadditive C Prod t Add) C1 t (@additive_terminal_object C Prod t Add) T0 P A B X D b c h))
  (@transf_arrow_diagram_func K C (@kernel_adjunction_family_func K C (@additive_preadditive C Prod t Add) t
  (@additive_terminal_object C Prod t Add) P (@transf_arrow_diagram_func K C B X b))
  (@kernel_adjunction_family_func K C (@additive_preadditive C Prod t Add) t (@additive_terminal_object C Prod t
  Add) P (@one_cat_native_snake_gamma_diagram K C (@additive_preadditive C Prod t Add) C1 t
  (@additive_terminal_object C Prod t Add) T0 Q A B X D b c h)) (@one_cat_native_snake_kernel_second K C
  (@additive_preadditive C Prod t Add) C1 t (@additive_terminal_object C Prod t Add) T0 P Q A B X D b c h))
  (@one_cat_native_snake_first_exact_input K C C1 Prod t Add T0 P Q N A B X D b c h)))
  (@kernel_adjunction_family_func K C (@additive_preadditive C Prod t Add) t (@additive_terminal_object C Prod t
  Add) P (@transf_arrow_diagram_func K C (@kernel_adjunction_family_func K C (@additive_preadditive C Prod t
  Add) t (@additive_terminal_object C Prod t Add) P (@transf_arrow_diagram_func K C B X b))
  (@kernel_adjunction_family_func K C (@additive_preadditive C Prod t Add) t (@additive_terminal_object C Prod t
  Add) P (@one_cat_native_snake_gamma_diagram K C (@additive_preadditive C Prod t Add) C1 t
  (@additive_terminal_object C Prod t Add) T0 Q A B X D b c h)) (@one_cat_native_snake_kernel_second K C
  (@additive_preadditive C Prod t Add) C1 t (@additive_terminal_object C Prod t Add) T0 P Q A B X D b c h)))
  (@one_cat_native_snake_first_exact_comparison K C C1 Prod t Add T0 P Q N A B X D b c h))) v (@comp_fapp0
  (Functor_cat K C) (@one_cat_native_snake_first_cover_source K C (@additive_preadditive C Prod t Add) C1 t
  (@additive_terminal_object C Prod t Add) T0 P Q A B X D b c h) (@kernel_adjunction_family_func K C
  (@additive_preadditive C Prod t Add) t (@additive_terminal_object C Prod t Add) P
  (@one_cat_native_snake_alpha_diagram K C (@additive_preadditive C Prod t Add) C1 t (@additive_terminal_object
  C Prod t Add) T0 P A B X D b c h)) (@comp_cat_fapp0 K (Functor_cat WalkingArrow_cat C) C
  (@adjunction_image_func C (@additive_preadditive C Prod t Add) t (@additive_terminal_object C Prod t Add) T0 P
  Q) (@zero_arrow_family_incoming_func K C t (@additive_terminal_object C Prod t Add)
  (@kernel_adjunction_family_func K C (@additive_preadditive C Prod t Add) t (@additive_terminal_object C Prod t
  Add) P (@one_cat_native_snake_alpha_diagram K C (@additive_preadditive C Prod t Add) C1 t
  (@additive_terminal_object C Prod t Add) T0 P A B X D b c h)) (@transf_arrow_diagram_func K C
  (@kernel_adjunction_family_func K C (@additive_preadditive C Prod t Add) t (@additive_terminal_object C Prod t
  Add) P (@transf_arrow_diagram_func K C B X b)) (@kernel_adjunction_family_func K C (@additive_preadditive C
  Prod t Add) t (@additive_terminal_object C Prod t Add) P (@one_cat_native_snake_gamma_diagram K C
  (@additive_preadditive C Prod t Add) C1 t (@additive_terminal_object C Prod t Add) T0 Q A B X D b c h))
  (@one_cat_native_snake_kernel_second K C (@additive_preadditive C Prod t Add) C1 t (@additive_terminal_object
  C Prod t Add) T0 P Q A B X D b c h)) (@one_cat_native_snake_first_exact_input K C C1 Prod t Add T0 P Q N A B X
  D b c h))) (@one_cat_image_family_source_transf K C (@additive_preadditive C Prod t Add) C1 t
  (@additive_terminal_object C Prod t Add) T0 P Q (@zero_arrow_family_incoming_func K C t
  (@additive_terminal_object C Prod t Add) (@kernel_adjunction_family_func K C (@additive_preadditive C Prod t
  Add) t (@additive_terminal_object C Prod t Add) P (@one_cat_native_snake_alpha_diagram K C
  (@additive_preadditive C Prod t Add) C1 t (@additive_terminal_object C Prod t Add) T0 P A B X D b c h))
  (@transf_arrow_diagram_func K C (@kernel_adjunction_family_func K C (@additive_preadditive C Prod t Add) t
  (@additive_terminal_object C Prod t Add) P (@transf_arrow_diagram_func K C B X b))
  (@kernel_adjunction_family_func K C (@additive_preadditive C Prod t Add) t (@additive_terminal_object C Prod t
  Add) P (@one_cat_native_snake_gamma_diagram K C (@additive_preadditive C Prod t Add) C1 t
  (@additive_terminal_object C Prod t Add) T0 Q A B X D b c h)) (@one_cat_native_snake_kernel_second K C
  (@additive_preadditive C Prod t Add) C1 t (@additive_terminal_object C Prod t Add) T0 P Q A B X D b c h))
  (@one_cat_native_snake_first_exact_input K C C1 Prod t Add T0 P Q N A B X D b c h)))
  (@one_cat_native_snake_first_cover_to_alpha_kernel K C (@additive_preadditive C Prod t Add) C1 t
  (@additive_terminal_object C Prod t Add) T0 P Q A B X D b c h)))) _ _
  (@one_cat_cokernel_family_annihilation_path K C (@additive_preadditive C Prod t Add) C1 t
  (@additive_terminal_object C Prod t Add) T0 Q (@transf_arrow_diagram_func K C (@comp_cat_fapp0 K (Functor_cat
  WalkingArrow_cat C) C (@adjunction_image_func C (@additive_preadditive C Prod t Add) t
  (@additive_terminal_object C Prod t Add) T0 P Q) (@zero_arrow_family_incoming_func K C t
  (@additive_terminal_object C Prod t Add) (@kernel_adjunction_family_func K C (@additive_preadditive C Prod t
  Add) t (@additive_terminal_object C Prod t Add) P (@one_cat_native_snake_alpha_diagram K C
  (@additive_preadditive C Prod t Add) C1 t (@additive_terminal_object C Prod t Add) T0 P A B X D b c h))
  (@transf_arrow_diagram_func K C (@kernel_adjunction_family_func K C (@additive_preadditive C Prod t Add) t
  (@additive_terminal_object C Prod t Add) P (@transf_arrow_diagram_func K C B X b))
  (@kernel_adjunction_family_func K C (@additive_preadditive C Prod t Add) t (@additive_terminal_object C Prod t
  Add) P (@one_cat_native_snake_gamma_diagram K C (@additive_preadditive C Prod t Add) C1 t
  (@additive_terminal_object C Prod t Add) T0 Q A B X D b c h)) (@one_cat_native_snake_kernel_second K C
  (@additive_preadditive C Prod t Add) C1 t (@additive_terminal_object C Prod t Add) T0 P Q A B X D b c h))
  (@one_cat_native_snake_first_exact_input K C C1 Prod t Add T0 P Q N A B X D b c h)))
  (@kernel_adjunction_family_func K C (@additive_preadditive C Prod t Add) t (@additive_terminal_object C Prod t
  Add) P (@transf_arrow_diagram_func K C (@kernel_adjunction_family_func K C (@additive_preadditive C Prod t
  Add) t (@additive_terminal_object C Prod t Add) P (@transf_arrow_diagram_func K C B X b))
  (@kernel_adjunction_family_func K C (@additive_preadditive C Prod t Add) t (@additive_terminal_object C Prod t
  Add) P (@one_cat_native_snake_gamma_diagram K C (@additive_preadditive C Prod t Add) C1 t
  (@additive_terminal_object C Prod t Add) T0 Q A B X D b c h)) (@one_cat_native_snake_kernel_second K C
  (@additive_preadditive C Prod t Add) C1 t (@additive_terminal_object C Prod t Add) T0 P Q A B X D b c h)))
  (@one_cat_native_snake_first_exact_comparison K C C1 Prod t Add T0 P Q N A B X D b c h)))) (@eq_trans _ _ _ _
  (@one_cat_zero_family_precompose_path K C C1 t (@additive_terminal_object C Prod t Add) T0
  (@one_cat_native_snake_first_cover_source K C (@additive_preadditive C Prod t Add) C1 t
  (@additive_terminal_object C Prod t Add) T0 P Q A B X D b c h) (@comp_cat_fapp0 K (Functor_cat
  WalkingArrow_cat C) C (@adjunction_image_func C (@additive_preadditive C Prod t Add) t
  (@additive_terminal_object C Prod t Add) T0 P Q) (@zero_arrow_family_incoming_func K C t
  (@additive_terminal_object C Prod t Add) (@kernel_adjunction_family_func K C (@additive_preadditive C Prod t
  Add) t (@additive_terminal_object C Prod t Add) P (@one_cat_native_snake_alpha_diagram K C
  (@additive_preadditive C Prod t Add) C1 t (@additive_terminal_object C Prod t Add) T0 P A B X D b c h))
  (@transf_arrow_diagram_func K C (@kernel_adjunction_family_func K C (@additive_preadditive C Prod t Add) t
  (@additive_terminal_object C Prod t Add) P (@transf_arrow_diagram_func K C B X b))
  (@kernel_adjunction_family_func K C (@additive_preadditive C Prod t Add) t (@additive_terminal_object C Prod t
  Add) P (@one_cat_native_snake_gamma_diagram K C (@additive_preadditive C Prod t Add) C1 t
  (@additive_terminal_object C Prod t Add) T0 Q A B X D b c h)) (@one_cat_native_snake_kernel_second K C
  (@additive_preadditive C Prod t Add) C1 t (@additive_terminal_object C Prod t Add) T0 P Q A B X D b c h))
  (@one_cat_native_snake_first_exact_input K C C1 Prod t Add T0 P Q N A B X D b c h)))
  (@cokernel_adjunction_family_func K C (@additive_preadditive C Prod t Add) t T0 Q (@transf_arrow_diagram_func
  K C (@comp_cat_fapp0 K (Functor_cat WalkingArrow_cat C) C (@adjunction_image_func C (@additive_preadditive C
  Prod t Add) t (@additive_terminal_object C Prod t Add) T0 P Q) (@zero_arrow_family_incoming_func K C t
  (@additive_terminal_object C Prod t Add) (@kernel_adjunction_family_func K C (@additive_preadditive C Prod t
  Add) t (@additive_terminal_object C Prod t Add) P (@one_cat_native_snake_alpha_diagram K C
  (@additive_preadditive C Prod t Add) C1 t (@additive_terminal_object C Prod t Add) T0 P A B X D b c h))
  (@transf_arrow_diagram_func K C (@kernel_adjunction_family_func K C (@additive_preadditive C Prod t Add) t
  (@additive_terminal_object C Prod t Add) P (@transf_arrow_diagram_func K C B X b))
  (@kernel_adjunction_family_func K C (@additive_preadditive C Prod t Add) t (@additive_terminal_object C Prod t
  Add) P (@one_cat_native_snake_gamma_diagram K C (@additive_preadditive C Prod t Add) C1 t
  (@additive_terminal_object C Prod t Add) T0 Q A B X D b c h)) (@one_cat_native_snake_kernel_second K C
  (@additive_preadditive C Prod t Add) C1 t (@additive_terminal_object C Prod t Add) T0 P Q A B X D b c h))
  (@one_cat_native_snake_first_exact_input K C C1 Prod t Add T0 P Q N A B X D b c h)))
  (@kernel_adjunction_family_func K C (@additive_preadditive C Prod t Add) t (@additive_terminal_object C Prod t
  Add) P (@transf_arrow_diagram_func K C (@kernel_adjunction_family_func K C (@additive_preadditive C Prod t
  Add) t (@additive_terminal_object C Prod t Add) P (@transf_arrow_diagram_func K C B X b))
  (@kernel_adjunction_family_func K C (@additive_preadditive C Prod t Add) t (@additive_terminal_object C Prod t
  Add) P (@one_cat_native_snake_gamma_diagram K C (@additive_preadditive C Prod t Add) C1 t
  (@additive_terminal_object C Prod t Add) T0 Q A B X D b c h)) (@one_cat_native_snake_kernel_second K C
  (@additive_preadditive C Prod t Add) C1 t (@additive_terminal_object C Prod t Add) T0 P Q A B X D b c h)))
  (@one_cat_native_snake_first_exact_comparison K C C1 Prod t Add T0 P Q N A B X D b c h))) (@comp_fapp0
  (Functor_cat K C) (@one_cat_native_snake_first_cover_source K C (@additive_preadditive C Prod t Add) C1 t
  (@additive_terminal_object C Prod t Add) T0 P Q A B X D b c h) (@kernel_adjunction_family_func K C
  (@additive_preadditive C Prod t Add) t (@additive_terminal_object C Prod t Add) P
  (@one_cat_native_snake_alpha_diagram K C (@additive_preadditive C Prod t Add) C1 t (@additive_terminal_object
  C Prod t Add) T0 P A B X D b c h)) (@comp_cat_fapp0 K (Functor_cat WalkingArrow_cat C) C
  (@adjunction_image_func C (@additive_preadditive C Prod t Add) t (@additive_terminal_object C Prod t Add) T0 P
  Q) (@zero_arrow_family_incoming_func K C t (@additive_terminal_object C Prod t Add)
  (@kernel_adjunction_family_func K C (@additive_preadditive C Prod t Add) t (@additive_terminal_object C Prod t
  Add) P (@one_cat_native_snake_alpha_diagram K C (@additive_preadditive C Prod t Add) C1 t
  (@additive_terminal_object C Prod t Add) T0 P A B X D b c h)) (@transf_arrow_diagram_func K C
  (@kernel_adjunction_family_func K C (@additive_preadditive C Prod t Add) t (@additive_terminal_object C Prod t
  Add) P (@transf_arrow_diagram_func K C B X b)) (@kernel_adjunction_family_func K C (@additive_preadditive C
  Prod t Add) t (@additive_terminal_object C Prod t Add) P (@one_cat_native_snake_gamma_diagram K C
  (@additive_preadditive C Prod t Add) C1 t (@additive_terminal_object C Prod t Add) T0 Q A B X D b c h))
  (@one_cat_native_snake_kernel_second K C (@additive_preadditive C Prod t Add) C1 t (@additive_terminal_object
  C Prod t Add) T0 P Q A B X D b c h)) (@one_cat_native_snake_first_exact_input K C C1 Prod t Add T0 P Q N A B X
  D b c h))) (@one_cat_image_family_source_transf K C (@additive_preadditive C Prod t Add) C1 t
  (@additive_terminal_object C Prod t Add) T0 P Q (@zero_arrow_family_incoming_func K C t
  (@additive_terminal_object C Prod t Add) (@kernel_adjunction_family_func K C (@additive_preadditive C Prod t
  Add) t (@additive_terminal_object C Prod t Add) P (@one_cat_native_snake_alpha_diagram K C
  (@additive_preadditive C Prod t Add) C1 t (@additive_terminal_object C Prod t Add) T0 P A B X D b c h))
  (@transf_arrow_diagram_func K C (@kernel_adjunction_family_func K C (@additive_preadditive C Prod t Add) t
  (@additive_terminal_object C Prod t Add) P (@transf_arrow_diagram_func K C B X b))
  (@kernel_adjunction_family_func K C (@additive_preadditive C Prod t Add) t (@additive_terminal_object C Prod t
  Add) P (@one_cat_native_snake_gamma_diagram K C (@additive_preadditive C Prod t Add) C1 t
  (@additive_terminal_object C Prod t Add) T0 Q A B X D b c h)) (@one_cat_native_snake_kernel_second K C
  (@additive_preadditive C Prod t Add) C1 t (@additive_terminal_object C Prod t Add) T0 P Q A B X D b c h))
  (@one_cat_native_snake_first_exact_input K C C1 Prod t Add T0 P Q N A B X D b c h)))
  (@one_cat_native_snake_first_cover_to_alpha_kernel K C (@additive_preadditive C Prod t Add) C1 t
  (@additive_terminal_object C Prod t Add) T0 P Q A B X D b c h))) (@eq_sym _ _ _
  (@one_cat_zero_family_precompose_path K C C1 t (@additive_terminal_object C Prod t Add) T0
  (@one_cat_native_snake_first_cover_source K C (@additive_preadditive C Prod t Add) C1 t
  (@additive_terminal_object C Prod t Add) T0 P Q A B X D b c h) (@kernel_adjunction_family_func K C
  (@additive_preadditive C Prod t Add) t (@additive_terminal_object C Prod t Add) P (@transf_arrow_diagram_func
  K C (@one_cat_native_snake_image_func K C (@additive_preadditive C Prod t Add) C1 t (@additive_terminal_object
  C Prod t Add) T0 P Q A B X D b c h) (@kernel_adjunction_family_func K C (@additive_preadditive C Prod t Add) t
  (@additive_terminal_object C Prod t Add) P (@transf_arrow_diagram_func K C X D c))
  (@one_cat_native_snake_image_lift K C (@additive_preadditive C Prod t Add) C1 t (@additive_terminal_object C
  Prod t Add) T0 P Q A B X D b c h))) (@cokernel_adjunction_family_func K C (@additive_preadditive C Prod t Add)
  t T0 Q (@transf_arrow_diagram_func K C (@comp_cat_fapp0 K (Functor_cat WalkingArrow_cat C) C
  (@adjunction_image_func C (@additive_preadditive C Prod t Add) t (@additive_terminal_object C Prod t Add) T0 P
  Q) (@zero_arrow_family_incoming_func K C t (@additive_terminal_object C Prod t Add)
  (@kernel_adjunction_family_func K C (@additive_preadditive C Prod t Add) t (@additive_terminal_object C Prod t
  Add) P (@one_cat_native_snake_alpha_diagram K C (@additive_preadditive C Prod t Add) C1 t
  (@additive_terminal_object C Prod t Add) T0 P A B X D b c h)) (@transf_arrow_diagram_func K C
  (@kernel_adjunction_family_func K C (@additive_preadditive C Prod t Add) t (@additive_terminal_object C Prod t
  Add) P (@transf_arrow_diagram_func K C B X b)) (@kernel_adjunction_family_func K C (@additive_preadditive C
  Prod t Add) t (@additive_terminal_object C Prod t Add) P (@one_cat_native_snake_gamma_diagram K C
  (@additive_preadditive C Prod t Add) C1 t (@additive_terminal_object C Prod t Add) T0 Q A B X D b c h))
  (@one_cat_native_snake_kernel_second K C (@additive_preadditive C Prod t Add) C1 t (@additive_terminal_object
  C Prod t Add) T0 P Q A B X D b c h)) (@one_cat_native_snake_first_exact_input K C C1 Prod t Add T0 P Q N A B X
  D b c h))) (@kernel_adjunction_family_func K C (@additive_preadditive C Prod t Add) t
  (@additive_terminal_object C Prod t Add) P (@transf_arrow_diagram_func K C (@kernel_adjunction_family_func K C
  (@additive_preadditive C Prod t Add) t (@additive_terminal_object C Prod t Add) P (@transf_arrow_diagram_func
  K C B X b)) (@kernel_adjunction_family_func K C (@additive_preadditive C Prod t Add) t
  (@additive_terminal_object C Prod t Add) P (@one_cat_native_snake_gamma_diagram K C (@additive_preadditive C
  Prod t Add) C1 t (@additive_terminal_object C Prod t Add) T0 Q A B X D b c h))
  (@one_cat_native_snake_kernel_second K C (@additive_preadditive C Prod t Add) C1 t (@additive_terminal_object
  C Prod t Add) T0 P Q A B X D b c h))) (@one_cat_native_snake_first_exact_comparison K C C1 Prod t Add T0 P Q N
  A B X D b c h))) (@one_cat_native_snake_first_cover_transf K C (@additive_preadditive C Prod t Add) C1 t
  (@additive_terminal_object C Prod t Add) T0 P Q A B X D b c h)))))))));

// The derived ηχ=id makes the actual first comparison cokernel projection zero.
symbol one_cat_native_snake_first_comparison_cokernel_zero [K C : Cat]
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
  : τ (@= (@Transf K C (@kernel_adjunction_family_func K C (@additive_preadditive C Prod t Add) t
    (@additive_terminal_object C Prod t Add) P (@transf_arrow_diagram_func K C (@kernel_adjunction_family_func K
    C (@additive_preadditive C Prod t Add) t (@additive_terminal_object C Prod t Add) P
    (@transf_arrow_diagram_func K C B X b)) (@kernel_adjunction_family_func K C (@additive_preadditive C Prod t
    Add) t (@additive_terminal_object C Prod t Add) P (@one_cat_native_snake_gamma_diagram K C
    (@additive_preadditive C Prod t Add) C1 t (@additive_terminal_object C Prod t Add) T0 Q A B X D b c h))
    (@one_cat_native_snake_kernel_second K C (@additive_preadditive C Prod t Add) C1 t
    (@additive_terminal_object C Prod t Add) T0 P Q A B X D b c h))) (@cokernel_adjunction_family_func K C
    (@additive_preadditive C Prod t Add) t T0 Q (@transf_arrow_diagram_func K C (@comp_cat_fapp0 K (Functor_cat
    WalkingArrow_cat C) C (@adjunction_image_func C (@additive_preadditive C Prod t Add) t
    (@additive_terminal_object C Prod t Add) T0 P Q) (@zero_arrow_family_incoming_func K C t
    (@additive_terminal_object C Prod t Add) (@kernel_adjunction_family_func K C (@additive_preadditive C Prod t
    Add) t (@additive_terminal_object C Prod t Add) P (@one_cat_native_snake_alpha_diagram K C
    (@additive_preadditive C Prod t Add) C1 t (@additive_terminal_object C Prod t Add) T0 P A B X D b c h))
    (@transf_arrow_diagram_func K C (@kernel_adjunction_family_func K C (@additive_preadditive C Prod t Add) t
    (@additive_terminal_object C Prod t Add) P (@transf_arrow_diagram_func K C B X b))
    (@kernel_adjunction_family_func K C (@additive_preadditive C Prod t Add) t (@additive_terminal_object C Prod
    t Add) P (@one_cat_native_snake_gamma_diagram K C (@additive_preadditive C Prod t Add) C1 t
    (@additive_terminal_object C Prod t Add) T0 Q A B X D b c h)) (@one_cat_native_snake_kernel_second K C
    (@additive_preadditive C Prod t Add) C1 t (@additive_terminal_object C Prod t Add) T0 P Q A B X D b c h))
    (@one_cat_native_snake_first_exact_input K C C1 Prod t Add T0 P Q N A B X D b c h)))
    (@kernel_adjunction_family_func K C (@additive_preadditive C Prod t Add) t (@additive_terminal_object C Prod
    t Add) P (@transf_arrow_diagram_func K C (@kernel_adjunction_family_func K C (@additive_preadditive C Prod t
    Add) t (@additive_terminal_object C Prod t Add) P (@transf_arrow_diagram_func K C B X b))
    (@kernel_adjunction_family_func K C (@additive_preadditive C Prod t Add) t (@additive_terminal_object C Prod
    t Add) P (@one_cat_native_snake_gamma_diagram K C (@additive_preadditive C Prod t Add) C1 t
    (@additive_terminal_object C Prod t Add) T0 Q A B X D b c h)) (@one_cat_native_snake_kernel_second K C
    (@additive_preadditive C Prod t Add) C1 t (@additive_terminal_object C Prod t Add) T0 P Q A B X D b c h)))
    (@one_cat_native_snake_first_exact_comparison K C C1 Prod t Add T0 P Q N A B X D b c h))))
    (@cokernel_adjunction_family_projection_transf K C (@additive_preadditive C Prod t Add) t T0 Q
    (@transf_arrow_diagram_func K C (@comp_cat_fapp0 K (Functor_cat WalkingArrow_cat C) C
    (@adjunction_image_func C (@additive_preadditive C Prod t Add) t (@additive_terminal_object C Prod t Add) T0
    P Q) (@zero_arrow_family_incoming_func K C t (@additive_terminal_object C Prod t Add)
    (@kernel_adjunction_family_func K C (@additive_preadditive C Prod t Add) t (@additive_terminal_object C Prod
    t Add) P (@one_cat_native_snake_alpha_diagram K C (@additive_preadditive C Prod t Add) C1 t
    (@additive_terminal_object C Prod t Add) T0 P A B X D b c h)) (@transf_arrow_diagram_func K C
    (@kernel_adjunction_family_func K C (@additive_preadditive C Prod t Add) t (@additive_terminal_object C Prod
    t Add) P (@transf_arrow_diagram_func K C B X b)) (@kernel_adjunction_family_func K C (@additive_preadditive
    C Prod t Add) t (@additive_terminal_object C Prod t Add) P (@one_cat_native_snake_gamma_diagram K C
    (@additive_preadditive C Prod t Add) C1 t (@additive_terminal_object C Prod t Add) T0 Q A B X D b c h))
    (@one_cat_native_snake_kernel_second K C (@additive_preadditive C Prod t Add) C1 t
    (@additive_terminal_object C Prod t Add) T0 P Q A B X D b c h)) (@one_cat_native_snake_first_exact_input K C
    C1 Prod t Add T0 P Q N A B X D b c h))) (@kernel_adjunction_family_func K C (@additive_preadditive C Prod t
    Add) t (@additive_terminal_object C Prod t Add) P (@transf_arrow_diagram_func K C
    (@kernel_adjunction_family_func K C (@additive_preadditive C Prod t Add) t (@additive_terminal_object C Prod
    t Add) P (@transf_arrow_diagram_func K C B X b)) (@kernel_adjunction_family_func K C (@additive_preadditive
    C Prod t Add) t (@additive_terminal_object C Prod t Add) P (@one_cat_native_snake_gamma_diagram K C
    (@additive_preadditive C Prod t Add) C1 t (@additive_terminal_object C Prod t Add) T0 Q A B X D b c h))
    (@one_cat_native_snake_kernel_second K C (@additive_preadditive C Prod t Add) C1 t
    (@additive_terminal_object C Prod t Add) T0 P Q A B X D b c h)))
    (@one_cat_native_snake_first_exact_comparison K C C1 Prod t Add T0 P Q N A B X D b c h)))
    (@zero_arrow_family_zero_transf K C t (@additive_terminal_object C Prod t Add) T0
    (@kernel_adjunction_family_func K C (@additive_preadditive C Prod t Add) t (@additive_terminal_object C Prod
    t Add) P (@transf_arrow_diagram_func K C (@kernel_adjunction_family_func K C (@additive_preadditive C Prod t
    Add) t (@additive_terminal_object C Prod t Add) P (@transf_arrow_diagram_func K C B X b))
    (@kernel_adjunction_family_func K C (@additive_preadditive C Prod t Add) t (@additive_terminal_object C Prod
    t Add) P (@one_cat_native_snake_gamma_diagram K C (@additive_preadditive C Prod t Add) C1 t
    (@additive_terminal_object C Prod t Add) T0 Q A B X D b c h)) (@one_cat_native_snake_kernel_second K C
    (@additive_preadditive C Prod t Add) C1 t (@additive_terminal_object C Prod t Add) T0 P Q A B X D b c h)))
    (@cokernel_adjunction_family_func K C (@additive_preadditive C Prod t Add) t T0 Q
    (@transf_arrow_diagram_func K C (@comp_cat_fapp0 K (Functor_cat WalkingArrow_cat C) C
    (@adjunction_image_func C (@additive_preadditive C Prod t Add) t (@additive_terminal_object C Prod t Add) T0
    P Q) (@zero_arrow_family_incoming_func K C t (@additive_terminal_object C Prod t Add)
    (@kernel_adjunction_family_func K C (@additive_preadditive C Prod t Add) t (@additive_terminal_object C Prod
    t Add) P (@one_cat_native_snake_alpha_diagram K C (@additive_preadditive C Prod t Add) C1 t
    (@additive_terminal_object C Prod t Add) T0 P A B X D b c h)) (@transf_arrow_diagram_func K C
    (@kernel_adjunction_family_func K C (@additive_preadditive C Prod t Add) t (@additive_terminal_object C Prod
    t Add) P (@transf_arrow_diagram_func K C B X b)) (@kernel_adjunction_family_func K C (@additive_preadditive
    C Prod t Add) t (@additive_terminal_object C Prod t Add) P (@one_cat_native_snake_gamma_diagram K C
    (@additive_preadditive C Prod t Add) C1 t (@additive_terminal_object C Prod t Add) T0 Q A B X D b c h))
    (@one_cat_native_snake_kernel_second K C (@additive_preadditive C Prod t Add) C1 t
    (@additive_terminal_object C Prod t Add) T0 P Q A B X D b c h)) (@one_cat_native_snake_first_exact_input K C
    C1 Prod t Add T0 P Q N A B X D b c h))) (@kernel_adjunction_family_func K C (@additive_preadditive C Prod t
    Add) t (@additive_terminal_object C Prod t Add) P (@transf_arrow_diagram_func K C
    (@kernel_adjunction_family_func K C (@additive_preadditive C Prod t Add) t (@additive_terminal_object C Prod
    t Add) P (@transf_arrow_diagram_func K C B X b)) (@kernel_adjunction_family_func K C (@additive_preadditive
    C Prod t Add) t (@additive_terminal_object C Prod t Add) P (@one_cat_native_snake_gamma_diagram K C
    (@additive_preadditive C Prod t Add) C1 t (@additive_terminal_object C Prod t Add) T0 Q A B X D b c h))
    (@one_cat_native_snake_kernel_second K C (@additive_preadditive C Prod t Add) C1 t
    (@additive_terminal_object C Prod t Add) T0 P Q A B X D b c h)))
    (@one_cat_native_snake_first_exact_comparison K C C1 Prod t Add T0 P Q N A B X D b c h)))))
≔ (@eq_trans _ _ _ _ (@eq_ap (@Transf K C (@kernel_adjunction_family_func K C (@additive_preadditive C Prod t
  Add) t (@additive_terminal_object C Prod t Add) P (@transf_arrow_diagram_func K C
  (@kernel_adjunction_family_func K C (@additive_preadditive C Prod t Add) t (@additive_terminal_object C Prod t
  Add) P (@transf_arrow_diagram_func K C B X b)) (@kernel_adjunction_family_func K C (@additive_preadditive C
  Prod t Add) t (@additive_terminal_object C Prod t Add) P (@one_cat_native_snake_gamma_diagram K C
  (@additive_preadditive C Prod t Add) C1 t (@additive_terminal_object C Prod t Add) T0 Q A B X D b c h))
  (@one_cat_native_snake_kernel_second K C (@additive_preadditive C Prod t Add) C1 t (@additive_terminal_object
  C Prod t Add) T0 P Q A B X D b c h))) (@kernel_adjunction_family_func K C (@additive_preadditive C Prod t Add)
  t (@additive_terminal_object C Prod t Add) P (@transf_arrow_diagram_func K C (@kernel_adjunction_family_func K
  C (@additive_preadditive C Prod t Add) t (@additive_terminal_object C Prod t Add) P
  (@transf_arrow_diagram_func K C B X b)) (@kernel_adjunction_family_func K C (@additive_preadditive C Prod t
  Add) t (@additive_terminal_object C Prod t Add) P (@one_cat_native_snake_gamma_diagram K C
  (@additive_preadditive C Prod t Add) C1 t (@additive_terminal_object C Prod t Add) T0 Q A B X D b c h))
  (@one_cat_native_snake_kernel_second K C (@additive_preadditive C Prod t Add) C1 t (@additive_terminal_object
  C Prod t Add) T0 P Q A B X D b c h)))) (@Transf K C (@kernel_adjunction_family_func K C (@additive_preadditive
  C Prod t Add) t (@additive_terminal_object C Prod t Add) P (@transf_arrow_diagram_func K C
  (@kernel_adjunction_family_func K C (@additive_preadditive C Prod t Add) t (@additive_terminal_object C Prod t
  Add) P (@transf_arrow_diagram_func K C B X b)) (@kernel_adjunction_family_func K C (@additive_preadditive C
  Prod t Add) t (@additive_terminal_object C Prod t Add) P (@one_cat_native_snake_gamma_diagram K C
  (@additive_preadditive C Prod t Add) C1 t (@additive_terminal_object C Prod t Add) T0 Q A B X D b c h))
  (@one_cat_native_snake_kernel_second K C (@additive_preadditive C Prod t Add) C1 t (@additive_terminal_object
  C Prod t Add) T0 P Q A B X D b c h))) (@cokernel_adjunction_family_func K C (@additive_preadditive C Prod t
  Add) t T0 Q (@transf_arrow_diagram_func K C (@comp_cat_fapp0 K (Functor_cat WalkingArrow_cat C) C
  (@adjunction_image_func C (@additive_preadditive C Prod t Add) t (@additive_terminal_object C Prod t Add) T0 P
  Q) (@zero_arrow_family_incoming_func K C t (@additive_terminal_object C Prod t Add)
  (@kernel_adjunction_family_func K C (@additive_preadditive C Prod t Add) t (@additive_terminal_object C Prod t
  Add) P (@one_cat_native_snake_alpha_diagram K C (@additive_preadditive C Prod t Add) C1 t
  (@additive_terminal_object C Prod t Add) T0 P A B X D b c h)) (@transf_arrow_diagram_func K C
  (@kernel_adjunction_family_func K C (@additive_preadditive C Prod t Add) t (@additive_terminal_object C Prod t
  Add) P (@transf_arrow_diagram_func K C B X b)) (@kernel_adjunction_family_func K C (@additive_preadditive C
  Prod t Add) t (@additive_terminal_object C Prod t Add) P (@one_cat_native_snake_gamma_diagram K C
  (@additive_preadditive C Prod t Add) C1 t (@additive_terminal_object C Prod t Add) T0 Q A B X D b c h))
  (@one_cat_native_snake_kernel_second K C (@additive_preadditive C Prod t Add) C1 t (@additive_terminal_object
  C Prod t Add) T0 P Q A B X D b c h)) (@one_cat_native_snake_first_exact_input K C C1 Prod t Add T0 P Q N A B X
  D b c h))) (@kernel_adjunction_family_func K C (@additive_preadditive C Prod t Add) t
  (@additive_terminal_object C Prod t Add) P (@transf_arrow_diagram_func K C (@kernel_adjunction_family_func K C
  (@additive_preadditive C Prod t Add) t (@additive_terminal_object C Prod t Add) P (@transf_arrow_diagram_func
  K C B X b)) (@kernel_adjunction_family_func K C (@additive_preadditive C Prod t Add) t
  (@additive_terminal_object C Prod t Add) P (@one_cat_native_snake_gamma_diagram K C (@additive_preadditive C
  Prod t Add) C1 t (@additive_terminal_object C Prod t Add) T0 Q A B X D b c h))
  (@one_cat_native_snake_kernel_second K C (@additive_preadditive C Prod t Add) C1 t (@additive_terminal_object
  C Prod t Add) T0 P Q A B X D b c h))) (@one_cat_native_snake_first_exact_comparison K C C1 Prod t Add T0 P Q N
  A B X D b c h)))) (λ w : τ (@Transf K C (@kernel_adjunction_family_func K C (@additive_preadditive C Prod t
  Add) t (@additive_terminal_object C Prod t Add) P (@transf_arrow_diagram_func K C
  (@kernel_adjunction_family_func K C (@additive_preadditive C Prod t Add) t (@additive_terminal_object C Prod t
  Add) P (@transf_arrow_diagram_func K C B X b)) (@kernel_adjunction_family_func K C (@additive_preadditive C
  Prod t Add) t (@additive_terminal_object C Prod t Add) P (@one_cat_native_snake_gamma_diagram K C
  (@additive_preadditive C Prod t Add) C1 t (@additive_terminal_object C Prod t Add) T0 Q A B X D b c h))
  (@one_cat_native_snake_kernel_second K C (@additive_preadditive C Prod t Add) C1 t (@additive_terminal_object
  C Prod t Add) T0 P Q A B X D b c h))) (@kernel_adjunction_family_func K C (@additive_preadditive C Prod t Add)
  t (@additive_terminal_object C Prod t Add) P (@transf_arrow_diagram_func K C (@kernel_adjunction_family_func K
  C (@additive_preadditive C Prod t Add) t (@additive_terminal_object C Prod t Add) P
  (@transf_arrow_diagram_func K C B X b)) (@kernel_adjunction_family_func K C (@additive_preadditive C Prod t
  Add) t (@additive_terminal_object C Prod t Add) P (@one_cat_native_snake_gamma_diagram K C
  (@additive_preadditive C Prod t Add) C1 t (@additive_terminal_object C Prod t Add) T0 Q A B X D b c h))
  (@one_cat_native_snake_kernel_second K C (@additive_preadditive C Prod t Add) C1 t (@additive_terminal_object
  C Prod t Add) T0 P Q A B X D b c h)))), (@comp_fapp0 (Functor_cat K C) (@kernel_adjunction_family_func K C
  (@additive_preadditive C Prod t Add) t (@additive_terminal_object C Prod t Add) P (@transf_arrow_diagram_func
  K C (@kernel_adjunction_family_func K C (@additive_preadditive C Prod t Add) t (@additive_terminal_object C
  Prod t Add) P (@transf_arrow_diagram_func K C B X b)) (@kernel_adjunction_family_func K C
  (@additive_preadditive C Prod t Add) t (@additive_terminal_object C Prod t Add) P
  (@one_cat_native_snake_gamma_diagram K C (@additive_preadditive C Prod t Add) C1 t (@additive_terminal_object
  C Prod t Add) T0 Q A B X D b c h)) (@one_cat_native_snake_kernel_second K C (@additive_preadditive C Prod t
  Add) C1 t (@additive_terminal_object C Prod t Add) T0 P Q A B X D b c h))) (@kernel_adjunction_family_func K C
  (@additive_preadditive C Prod t Add) t (@additive_terminal_object C Prod t Add) P (@transf_arrow_diagram_func
  K C (@kernel_adjunction_family_func K C (@additive_preadditive C Prod t Add) t (@additive_terminal_object C
  Prod t Add) P (@transf_arrow_diagram_func K C B X b)) (@kernel_adjunction_family_func K C
  (@additive_preadditive C Prod t Add) t (@additive_terminal_object C Prod t Add) P
  (@one_cat_native_snake_gamma_diagram K C (@additive_preadditive C Prod t Add) C1 t (@additive_terminal_object
  C Prod t Add) T0 Q A B X D b c h)) (@one_cat_native_snake_kernel_second K C (@additive_preadditive C Prod t
  Add) C1 t (@additive_terminal_object C Prod t Add) T0 P Q A B X D b c h))) (@cokernel_adjunction_family_func K
  C (@additive_preadditive C Prod t Add) t T0 Q (@transf_arrow_diagram_func K C (@comp_cat_fapp0 K (Functor_cat
  WalkingArrow_cat C) C (@adjunction_image_func C (@additive_preadditive C Prod t Add) t
  (@additive_terminal_object C Prod t Add) T0 P Q) (@zero_arrow_family_incoming_func K C t
  (@additive_terminal_object C Prod t Add) (@kernel_adjunction_family_func K C (@additive_preadditive C Prod t
  Add) t (@additive_terminal_object C Prod t Add) P (@one_cat_native_snake_alpha_diagram K C
  (@additive_preadditive C Prod t Add) C1 t (@additive_terminal_object C Prod t Add) T0 P A B X D b c h))
  (@transf_arrow_diagram_func K C (@kernel_adjunction_family_func K C (@additive_preadditive C Prod t Add) t
  (@additive_terminal_object C Prod t Add) P (@transf_arrow_diagram_func K C B X b))
  (@kernel_adjunction_family_func K C (@additive_preadditive C Prod t Add) t (@additive_terminal_object C Prod t
  Add) P (@one_cat_native_snake_gamma_diagram K C (@additive_preadditive C Prod t Add) C1 t
  (@additive_terminal_object C Prod t Add) T0 Q A B X D b c h)) (@one_cat_native_snake_kernel_second K C
  (@additive_preadditive C Prod t Add) C1 t (@additive_terminal_object C Prod t Add) T0 P Q A B X D b c h))
  (@one_cat_native_snake_first_exact_input K C C1 Prod t Add T0 P Q N A B X D b c h)))
  (@kernel_adjunction_family_func K C (@additive_preadditive C Prod t Add) t (@additive_terminal_object C Prod t
  Add) P (@transf_arrow_diagram_func K C (@kernel_adjunction_family_func K C (@additive_preadditive C Prod t
  Add) t (@additive_terminal_object C Prod t Add) P (@transf_arrow_diagram_func K C B X b))
  (@kernel_adjunction_family_func K C (@additive_preadditive C Prod t Add) t (@additive_terminal_object C Prod t
  Add) P (@one_cat_native_snake_gamma_diagram K C (@additive_preadditive C Prod t Add) C1 t
  (@additive_terminal_object C Prod t Add) T0 Q A B X D b c h)) (@one_cat_native_snake_kernel_second K C
  (@additive_preadditive C Prod t Add) C1 t (@additive_terminal_object C Prod t Add) T0 P Q A B X D b c h)))
  (@one_cat_native_snake_first_exact_comparison K C C1 Prod t Add T0 P Q N A B X D b c h)))
  (@cokernel_adjunction_family_projection_transf K C (@additive_preadditive C Prod t Add) t T0 Q
  (@transf_arrow_diagram_func K C (@comp_cat_fapp0 K (Functor_cat WalkingArrow_cat C) C (@adjunction_image_func
  C (@additive_preadditive C Prod t Add) t (@additive_terminal_object C Prod t Add) T0 P Q)
  (@zero_arrow_family_incoming_func K C t (@additive_terminal_object C Prod t Add)
  (@kernel_adjunction_family_func K C (@additive_preadditive C Prod t Add) t (@additive_terminal_object C Prod t
  Add) P (@one_cat_native_snake_alpha_diagram K C (@additive_preadditive C Prod t Add) C1 t
  (@additive_terminal_object C Prod t Add) T0 P A B X D b c h)) (@transf_arrow_diagram_func K C
  (@kernel_adjunction_family_func K C (@additive_preadditive C Prod t Add) t (@additive_terminal_object C Prod t
  Add) P (@transf_arrow_diagram_func K C B X b)) (@kernel_adjunction_family_func K C (@additive_preadditive C
  Prod t Add) t (@additive_terminal_object C Prod t Add) P (@one_cat_native_snake_gamma_diagram K C
  (@additive_preadditive C Prod t Add) C1 t (@additive_terminal_object C Prod t Add) T0 Q A B X D b c h))
  (@one_cat_native_snake_kernel_second K C (@additive_preadditive C Prod t Add) C1 t (@additive_terminal_object
  C Prod t Add) T0 P Q A B X D b c h)) (@one_cat_native_snake_first_exact_input K C C1 Prod t Add T0 P Q N A B X
  D b c h))) (@kernel_adjunction_family_func K C (@additive_preadditive C Prod t Add) t
  (@additive_terminal_object C Prod t Add) P (@transf_arrow_diagram_func K C (@kernel_adjunction_family_func K C
  (@additive_preadditive C Prod t Add) t (@additive_terminal_object C Prod t Add) P (@transf_arrow_diagram_func
  K C B X b)) (@kernel_adjunction_family_func K C (@additive_preadditive C Prod t Add) t
  (@additive_terminal_object C Prod t Add) P (@one_cat_native_snake_gamma_diagram K C (@additive_preadditive C
  Prod t Add) C1 t (@additive_terminal_object C Prod t Add) T0 Q A B X D b c h))
  (@one_cat_native_snake_kernel_second K C (@additive_preadditive C Prod t Add) C1 t (@additive_terminal_object
  C Prod t Add) T0 P Q A B X D b c h))) (@one_cat_native_snake_first_exact_comparison K C C1 Prod t Add T0 P Q N
  A B X D b c h))) w)) (@id (Functor_cat K C) (@kernel_adjunction_family_func K C (@additive_preadditive C Prod
  t Add) t (@additive_terminal_object C Prod t Add) P (@transf_arrow_diagram_func K C
  (@kernel_adjunction_family_func K C (@additive_preadditive C Prod t Add) t (@additive_terminal_object C Prod t
  Add) P (@transf_arrow_diagram_func K C B X b)) (@kernel_adjunction_family_func K C (@additive_preadditive C
  Prod t Add) t (@additive_terminal_object C Prod t Add) P (@one_cat_native_snake_gamma_diagram K C
  (@additive_preadditive C Prod t Add) C1 t (@additive_terminal_object C Prod t Add) T0 Q A B X D b c h))
  (@one_cat_native_snake_kernel_second K C (@additive_preadditive C Prod t Add) C1 t (@additive_terminal_object
  C Prod t Add) T0 P Q A B X D b c h)))) (@comp_fapp0 (Functor_cat K C) (@kernel_adjunction_family_func K C
  (@additive_preadditive C Prod t Add) t (@additive_terminal_object C Prod t Add) P (@transf_arrow_diagram_func
  K C (@kernel_adjunction_family_func K C (@additive_preadditive C Prod t Add) t (@additive_terminal_object C
  Prod t Add) P (@transf_arrow_diagram_func K C B X b)) (@kernel_adjunction_family_func K C
  (@additive_preadditive C Prod t Add) t (@additive_terminal_object C Prod t Add) P
  (@one_cat_native_snake_gamma_diagram K C (@additive_preadditive C Prod t Add) C1 t (@additive_terminal_object
  C Prod t Add) T0 Q A B X D b c h)) (@one_cat_native_snake_kernel_second K C (@additive_preadditive C Prod t
  Add) C1 t (@additive_terminal_object C Prod t Add) T0 P Q A B X D b c h))) (@kernel_adjunction_family_func K C
  (@additive_preadditive C Prod t Add) t (@additive_terminal_object C Prod t Add) P (@transf_arrow_diagram_func
  K C (@one_cat_native_snake_image_func K C (@additive_preadditive C Prod t Add) C1 t (@additive_terminal_object
  C Prod t Add) T0 P Q A B X D b c h) (@kernel_adjunction_family_func K C (@additive_preadditive C Prod t Add) t
  (@additive_terminal_object C Prod t Add) P (@transf_arrow_diagram_func K C X D c))
  (@one_cat_native_snake_image_lift K C (@additive_preadditive C Prod t Add) C1 t (@additive_terminal_object C
  Prod t Add) T0 P Q A B X D b c h))) (@kernel_adjunction_family_func K C (@additive_preadditive C Prod t Add) t
  (@additive_terminal_object C Prod t Add) P (@transf_arrow_diagram_func K C (@kernel_adjunction_family_func K C
  (@additive_preadditive C Prod t Add) t (@additive_terminal_object C Prod t Add) P (@transf_arrow_diagram_func
  K C B X b)) (@kernel_adjunction_family_func K C (@additive_preadditive C Prod t Add) t
  (@additive_terminal_object C Prod t Add) P (@one_cat_native_snake_gamma_diagram K C (@additive_preadditive C
  Prod t Add) C1 t (@additive_terminal_object C Prod t Add) T0 Q A B X D b c h))
  (@one_cat_native_snake_kernel_second K C (@additive_preadditive C Prod t Add) C1 t (@additive_terminal_object
  C Prod t Add) T0 P Q A B X D b c h))) (@one_cat_native_snake_first_image_kernel_to_kernel K C
  (@additive_preadditive C Prod t Add) C1 t (@additive_terminal_object C Prod t Add) T0 P Q A B X D b c h)
  (@one_cat_native_snake_first_kernel_to_image_kernel K C (@additive_preadditive C Prod t Add) C1 t
  (@additive_terminal_object C Prod t Add) T0 P Q A B X D b c h)) (@eq_sym _ _ _
  (@one_cat_native_snake_first_kernel_retraction_path K C (@additive_preadditive C Prod t Add) C1 t
  (@additive_terminal_object C Prod t Add) T0 P Q A B X D b c h))) (@eq_trans _ _ _ _ (@comp_assoc (Functor_cat
  K C) (@kernel_adjunction_family_func K C (@additive_preadditive C Prod t Add) t (@additive_terminal_object C
  Prod t Add) P (@transf_arrow_diagram_func K C (@kernel_adjunction_family_func K C (@additive_preadditive C
  Prod t Add) t (@additive_terminal_object C Prod t Add) P (@transf_arrow_diagram_func K C B X b))
  (@kernel_adjunction_family_func K C (@additive_preadditive C Prod t Add) t (@additive_terminal_object C Prod t
  Add) P (@one_cat_native_snake_gamma_diagram K C (@additive_preadditive C Prod t Add) C1 t
  (@additive_terminal_object C Prod t Add) T0 Q A B X D b c h)) (@one_cat_native_snake_kernel_second K C
  (@additive_preadditive C Prod t Add) C1 t (@additive_terminal_object C Prod t Add) T0 P Q A B X D b c h)))
  (@kernel_adjunction_family_func K C (@additive_preadditive C Prod t Add) t (@additive_terminal_object C Prod t
  Add) P (@transf_arrow_diagram_func K C (@one_cat_native_snake_image_func K C (@additive_preadditive C Prod t
  Add) C1 t (@additive_terminal_object C Prod t Add) T0 P Q A B X D b c h) (@kernel_adjunction_family_func K C
  (@additive_preadditive C Prod t Add) t (@additive_terminal_object C Prod t Add) P (@transf_arrow_diagram_func
  K C X D c)) (@one_cat_native_snake_image_lift K C (@additive_preadditive C Prod t Add) C1 t
  (@additive_terminal_object C Prod t Add) T0 P Q A B X D b c h))) (@kernel_adjunction_family_func K C
  (@additive_preadditive C Prod t Add) t (@additive_terminal_object C Prod t Add) P (@transf_arrow_diagram_func
  K C (@kernel_adjunction_family_func K C (@additive_preadditive C Prod t Add) t (@additive_terminal_object C
  Prod t Add) P (@transf_arrow_diagram_func K C B X b)) (@kernel_adjunction_family_func K C
  (@additive_preadditive C Prod t Add) t (@additive_terminal_object C Prod t Add) P
  (@one_cat_native_snake_gamma_diagram K C (@additive_preadditive C Prod t Add) C1 t (@additive_terminal_object
  C Prod t Add) T0 Q A B X D b c h)) (@one_cat_native_snake_kernel_second K C (@additive_preadditive C Prod t
  Add) C1 t (@additive_terminal_object C Prod t Add) T0 P Q A B X D b c h))) (@cokernel_adjunction_family_func K
  C (@additive_preadditive C Prod t Add) t T0 Q (@transf_arrow_diagram_func K C (@comp_cat_fapp0 K (Functor_cat
  WalkingArrow_cat C) C (@adjunction_image_func C (@additive_preadditive C Prod t Add) t
  (@additive_terminal_object C Prod t Add) T0 P Q) (@zero_arrow_family_incoming_func K C t
  (@additive_terminal_object C Prod t Add) (@kernel_adjunction_family_func K C (@additive_preadditive C Prod t
  Add) t (@additive_terminal_object C Prod t Add) P (@one_cat_native_snake_alpha_diagram K C
  (@additive_preadditive C Prod t Add) C1 t (@additive_terminal_object C Prod t Add) T0 P A B X D b c h))
  (@transf_arrow_diagram_func K C (@kernel_adjunction_family_func K C (@additive_preadditive C Prod t Add) t
  (@additive_terminal_object C Prod t Add) P (@transf_arrow_diagram_func K C B X b))
  (@kernel_adjunction_family_func K C (@additive_preadditive C Prod t Add) t (@additive_terminal_object C Prod t
  Add) P (@one_cat_native_snake_gamma_diagram K C (@additive_preadditive C Prod t Add) C1 t
  (@additive_terminal_object C Prod t Add) T0 Q A B X D b c h)) (@one_cat_native_snake_kernel_second K C
  (@additive_preadditive C Prod t Add) C1 t (@additive_terminal_object C Prod t Add) T0 P Q A B X D b c h))
  (@one_cat_native_snake_first_exact_input K C C1 Prod t Add T0 P Q N A B X D b c h)))
  (@kernel_adjunction_family_func K C (@additive_preadditive C Prod t Add) t (@additive_terminal_object C Prod t
  Add) P (@transf_arrow_diagram_func K C (@kernel_adjunction_family_func K C (@additive_preadditive C Prod t
  Add) t (@additive_terminal_object C Prod t Add) P (@transf_arrow_diagram_func K C B X b))
  (@kernel_adjunction_family_func K C (@additive_preadditive C Prod t Add) t (@additive_terminal_object C Prod t
  Add) P (@one_cat_native_snake_gamma_diagram K C (@additive_preadditive C Prod t Add) C1 t
  (@additive_terminal_object C Prod t Add) T0 Q A B X D b c h)) (@one_cat_native_snake_kernel_second K C
  (@additive_preadditive C Prod t Add) C1 t (@additive_terminal_object C Prod t Add) T0 P Q A B X D b c h)))
  (@one_cat_native_snake_first_exact_comparison K C C1 Prod t Add T0 P Q N A B X D b c h)))
  (@cokernel_adjunction_family_projection_transf K C (@additive_preadditive C Prod t Add) t T0 Q
  (@transf_arrow_diagram_func K C (@comp_cat_fapp0 K (Functor_cat WalkingArrow_cat C) C (@adjunction_image_func
  C (@additive_preadditive C Prod t Add) t (@additive_terminal_object C Prod t Add) T0 P Q)
  (@zero_arrow_family_incoming_func K C t (@additive_terminal_object C Prod t Add)
  (@kernel_adjunction_family_func K C (@additive_preadditive C Prod t Add) t (@additive_terminal_object C Prod t
  Add) P (@one_cat_native_snake_alpha_diagram K C (@additive_preadditive C Prod t Add) C1 t
  (@additive_terminal_object C Prod t Add) T0 P A B X D b c h)) (@transf_arrow_diagram_func K C
  (@kernel_adjunction_family_func K C (@additive_preadditive C Prod t Add) t (@additive_terminal_object C Prod t
  Add) P (@transf_arrow_diagram_func K C B X b)) (@kernel_adjunction_family_func K C (@additive_preadditive C
  Prod t Add) t (@additive_terminal_object C Prod t Add) P (@one_cat_native_snake_gamma_diagram K C
  (@additive_preadditive C Prod t Add) C1 t (@additive_terminal_object C Prod t Add) T0 Q A B X D b c h))
  (@one_cat_native_snake_kernel_second K C (@additive_preadditive C Prod t Add) C1 t (@additive_terminal_object
  C Prod t Add) T0 P Q A B X D b c h)) (@one_cat_native_snake_first_exact_input K C C1 Prod t Add T0 P Q N A B X
  D b c h))) (@kernel_adjunction_family_func K C (@additive_preadditive C Prod t Add) t
  (@additive_terminal_object C Prod t Add) P (@transf_arrow_diagram_func K C (@kernel_adjunction_family_func K C
  (@additive_preadditive C Prod t Add) t (@additive_terminal_object C Prod t Add) P (@transf_arrow_diagram_func
  K C B X b)) (@kernel_adjunction_family_func K C (@additive_preadditive C Prod t Add) t
  (@additive_terminal_object C Prod t Add) P (@one_cat_native_snake_gamma_diagram K C (@additive_preadditive C
  Prod t Add) C1 t (@additive_terminal_object C Prod t Add) T0 Q A B X D b c h))
  (@one_cat_native_snake_kernel_second K C (@additive_preadditive C Prod t Add) C1 t (@additive_terminal_object
  C Prod t Add) T0 P Q A B X D b c h))) (@one_cat_native_snake_first_exact_comparison K C C1 Prod t Add T0 P Q N
  A B X D b c h))) (@one_cat_native_snake_first_image_kernel_to_kernel K C (@additive_preadditive C Prod t Add)
  C1 t (@additive_terminal_object C Prod t Add) T0 P Q A B X D b c h)
  (@one_cat_native_snake_first_kernel_to_image_kernel K C (@additive_preadditive C Prod t Add) C1 t
  (@additive_terminal_object C Prod t Add) T0 P Q A B X D b c h)) (@eq_trans _ _ _ _ (@eq_ap (@Transf K C
  (@kernel_adjunction_family_func K C (@additive_preadditive C Prod t Add) t (@additive_terminal_object C Prod t
  Add) P (@transf_arrow_diagram_func K C (@one_cat_native_snake_image_func K C (@additive_preadditive C Prod t
  Add) C1 t (@additive_terminal_object C Prod t Add) T0 P Q A B X D b c h) (@kernel_adjunction_family_func K C
  (@additive_preadditive C Prod t Add) t (@additive_terminal_object C Prod t Add) P (@transf_arrow_diagram_func
  K C X D c)) (@one_cat_native_snake_image_lift K C (@additive_preadditive C Prod t Add) C1 t
  (@additive_terminal_object C Prod t Add) T0 P Q A B X D b c h))) (@cokernel_adjunction_family_func K C
  (@additive_preadditive C Prod t Add) t T0 Q (@transf_arrow_diagram_func K C (@comp_cat_fapp0 K (Functor_cat
  WalkingArrow_cat C) C (@adjunction_image_func C (@additive_preadditive C Prod t Add) t
  (@additive_terminal_object C Prod t Add) T0 P Q) (@zero_arrow_family_incoming_func K C t
  (@additive_terminal_object C Prod t Add) (@kernel_adjunction_family_func K C (@additive_preadditive C Prod t
  Add) t (@additive_terminal_object C Prod t Add) P (@one_cat_native_snake_alpha_diagram K C
  (@additive_preadditive C Prod t Add) C1 t (@additive_terminal_object C Prod t Add) T0 P A B X D b c h))
  (@transf_arrow_diagram_func K C (@kernel_adjunction_family_func K C (@additive_preadditive C Prod t Add) t
  (@additive_terminal_object C Prod t Add) P (@transf_arrow_diagram_func K C B X b))
  (@kernel_adjunction_family_func K C (@additive_preadditive C Prod t Add) t (@additive_terminal_object C Prod t
  Add) P (@one_cat_native_snake_gamma_diagram K C (@additive_preadditive C Prod t Add) C1 t
  (@additive_terminal_object C Prod t Add) T0 Q A B X D b c h)) (@one_cat_native_snake_kernel_second K C
  (@additive_preadditive C Prod t Add) C1 t (@additive_terminal_object C Prod t Add) T0 P Q A B X D b c h))
  (@one_cat_native_snake_first_exact_input K C C1 Prod t Add T0 P Q N A B X D b c h)))
  (@kernel_adjunction_family_func K C (@additive_preadditive C Prod t Add) t (@additive_terminal_object C Prod t
  Add) P (@transf_arrow_diagram_func K C (@kernel_adjunction_family_func K C (@additive_preadditive C Prod t
  Add) t (@additive_terminal_object C Prod t Add) P (@transf_arrow_diagram_func K C B X b))
  (@kernel_adjunction_family_func K C (@additive_preadditive C Prod t Add) t (@additive_terminal_object C Prod t
  Add) P (@one_cat_native_snake_gamma_diagram K C (@additive_preadditive C Prod t Add) C1 t
  (@additive_terminal_object C Prod t Add) T0 Q A B X D b c h)) (@one_cat_native_snake_kernel_second K C
  (@additive_preadditive C Prod t Add) C1 t (@additive_terminal_object C Prod t Add) T0 P Q A B X D b c h)))
  (@one_cat_native_snake_first_exact_comparison K C C1 Prod t Add T0 P Q N A B X D b c h)))) (@Transf K C
  (@kernel_adjunction_family_func K C (@additive_preadditive C Prod t Add) t (@additive_terminal_object C Prod t
  Add) P (@transf_arrow_diagram_func K C (@kernel_adjunction_family_func K C (@additive_preadditive C Prod t
  Add) t (@additive_terminal_object C Prod t Add) P (@transf_arrow_diagram_func K C B X b))
  (@kernel_adjunction_family_func K C (@additive_preadditive C Prod t Add) t (@additive_terminal_object C Prod t
  Add) P (@one_cat_native_snake_gamma_diagram K C (@additive_preadditive C Prod t Add) C1 t
  (@additive_terminal_object C Prod t Add) T0 Q A B X D b c h)) (@one_cat_native_snake_kernel_second K C
  (@additive_preadditive C Prod t Add) C1 t (@additive_terminal_object C Prod t Add) T0 P Q A B X D b c h)))
  (@cokernel_adjunction_family_func K C (@additive_preadditive C Prod t Add) t T0 Q (@transf_arrow_diagram_func
  K C (@comp_cat_fapp0 K (Functor_cat WalkingArrow_cat C) C (@adjunction_image_func C (@additive_preadditive C
  Prod t Add) t (@additive_terminal_object C Prod t Add) T0 P Q) (@zero_arrow_family_incoming_func K C t
  (@additive_terminal_object C Prod t Add) (@kernel_adjunction_family_func K C (@additive_preadditive C Prod t
  Add) t (@additive_terminal_object C Prod t Add) P (@one_cat_native_snake_alpha_diagram K C
  (@additive_preadditive C Prod t Add) C1 t (@additive_terminal_object C Prod t Add) T0 P A B X D b c h))
  (@transf_arrow_diagram_func K C (@kernel_adjunction_family_func K C (@additive_preadditive C Prod t Add) t
  (@additive_terminal_object C Prod t Add) P (@transf_arrow_diagram_func K C B X b))
  (@kernel_adjunction_family_func K C (@additive_preadditive C Prod t Add) t (@additive_terminal_object C Prod t
  Add) P (@one_cat_native_snake_gamma_diagram K C (@additive_preadditive C Prod t Add) C1 t
  (@additive_terminal_object C Prod t Add) T0 Q A B X D b c h)) (@one_cat_native_snake_kernel_second K C
  (@additive_preadditive C Prod t Add) C1 t (@additive_terminal_object C Prod t Add) T0 P Q A B X D b c h))
  (@one_cat_native_snake_first_exact_input K C C1 Prod t Add T0 P Q N A B X D b c h)))
  (@kernel_adjunction_family_func K C (@additive_preadditive C Prod t Add) t (@additive_terminal_object C Prod t
  Add) P (@transf_arrow_diagram_func K C (@kernel_adjunction_family_func K C (@additive_preadditive C Prod t
  Add) t (@additive_terminal_object C Prod t Add) P (@transf_arrow_diagram_func K C B X b))
  (@kernel_adjunction_family_func K C (@additive_preadditive C Prod t Add) t (@additive_terminal_object C Prod t
  Add) P (@one_cat_native_snake_gamma_diagram K C (@additive_preadditive C Prod t Add) C1 t
  (@additive_terminal_object C Prod t Add) T0 Q A B X D b c h)) (@one_cat_native_snake_kernel_second K C
  (@additive_preadditive C Prod t Add) C1 t (@additive_terminal_object C Prod t Add) T0 P Q A B X D b c h)))
  (@one_cat_native_snake_first_exact_comparison K C C1 Prod t Add T0 P Q N A B X D b c h)))) (λ v : τ (@Transf K
  C (@kernel_adjunction_family_func K C (@additive_preadditive C Prod t Add) t (@additive_terminal_object C Prod
  t Add) P (@transf_arrow_diagram_func K C (@one_cat_native_snake_image_func K C (@additive_preadditive C Prod t
  Add) C1 t (@additive_terminal_object C Prod t Add) T0 P Q A B X D b c h) (@kernel_adjunction_family_func K C
  (@additive_preadditive C Prod t Add) t (@additive_terminal_object C Prod t Add) P (@transf_arrow_diagram_func
  K C X D c)) (@one_cat_native_snake_image_lift K C (@additive_preadditive C Prod t Add) C1 t
  (@additive_terminal_object C Prod t Add) T0 P Q A B X D b c h))) (@cokernel_adjunction_family_func K C
  (@additive_preadditive C Prod t Add) t T0 Q (@transf_arrow_diagram_func K C (@comp_cat_fapp0 K (Functor_cat
  WalkingArrow_cat C) C (@adjunction_image_func C (@additive_preadditive C Prod t Add) t
  (@additive_terminal_object C Prod t Add) T0 P Q) (@zero_arrow_family_incoming_func K C t
  (@additive_terminal_object C Prod t Add) (@kernel_adjunction_family_func K C (@additive_preadditive C Prod t
  Add) t (@additive_terminal_object C Prod t Add) P (@one_cat_native_snake_alpha_diagram K C
  (@additive_preadditive C Prod t Add) C1 t (@additive_terminal_object C Prod t Add) T0 P A B X D b c h))
  (@transf_arrow_diagram_func K C (@kernel_adjunction_family_func K C (@additive_preadditive C Prod t Add) t
  (@additive_terminal_object C Prod t Add) P (@transf_arrow_diagram_func K C B X b))
  (@kernel_adjunction_family_func K C (@additive_preadditive C Prod t Add) t (@additive_terminal_object C Prod t
  Add) P (@one_cat_native_snake_gamma_diagram K C (@additive_preadditive C Prod t Add) C1 t
  (@additive_terminal_object C Prod t Add) T0 Q A B X D b c h)) (@one_cat_native_snake_kernel_second K C
  (@additive_preadditive C Prod t Add) C1 t (@additive_terminal_object C Prod t Add) T0 P Q A B X D b c h))
  (@one_cat_native_snake_first_exact_input K C C1 Prod t Add T0 P Q N A B X D b c h)))
  (@kernel_adjunction_family_func K C (@additive_preadditive C Prod t Add) t (@additive_terminal_object C Prod t
  Add) P (@transf_arrow_diagram_func K C (@kernel_adjunction_family_func K C (@additive_preadditive C Prod t
  Add) t (@additive_terminal_object C Prod t Add) P (@transf_arrow_diagram_func K C B X b))
  (@kernel_adjunction_family_func K C (@additive_preadditive C Prod t Add) t (@additive_terminal_object C Prod t
  Add) P (@one_cat_native_snake_gamma_diagram K C (@additive_preadditive C Prod t Add) C1 t
  (@additive_terminal_object C Prod t Add) T0 Q A B X D b c h)) (@one_cat_native_snake_kernel_second K C
  (@additive_preadditive C Prod t Add) C1 t (@additive_terminal_object C Prod t Add) T0 P Q A B X D b c h)))
  (@one_cat_native_snake_first_exact_comparison K C C1 Prod t Add T0 P Q N A B X D b c h)))), (@comp_fapp0
  (Functor_cat K C) (@kernel_adjunction_family_func K C (@additive_preadditive C Prod t Add) t
  (@additive_terminal_object C Prod t Add) P (@transf_arrow_diagram_func K C (@kernel_adjunction_family_func K C
  (@additive_preadditive C Prod t Add) t (@additive_terminal_object C Prod t Add) P (@transf_arrow_diagram_func
  K C B X b)) (@kernel_adjunction_family_func K C (@additive_preadditive C Prod t Add) t
  (@additive_terminal_object C Prod t Add) P (@one_cat_native_snake_gamma_diagram K C (@additive_preadditive C
  Prod t Add) C1 t (@additive_terminal_object C Prod t Add) T0 Q A B X D b c h))
  (@one_cat_native_snake_kernel_second K C (@additive_preadditive C Prod t Add) C1 t (@additive_terminal_object
  C Prod t Add) T0 P Q A B X D b c h))) (@kernel_adjunction_family_func K C (@additive_preadditive C Prod t Add)
  t (@additive_terminal_object C Prod t Add) P (@transf_arrow_diagram_func K C (@one_cat_native_snake_image_func
  K C (@additive_preadditive C Prod t Add) C1 t (@additive_terminal_object C Prod t Add) T0 P Q A B X D b c h)
  (@kernel_adjunction_family_func K C (@additive_preadditive C Prod t Add) t (@additive_terminal_object C Prod t
  Add) P (@transf_arrow_diagram_func K C X D c)) (@one_cat_native_snake_image_lift K C (@additive_preadditive C
  Prod t Add) C1 t (@additive_terminal_object C Prod t Add) T0 P Q A B X D b c h)))
  (@cokernel_adjunction_family_func K C (@additive_preadditive C Prod t Add) t T0 Q (@transf_arrow_diagram_func
  K C (@comp_cat_fapp0 K (Functor_cat WalkingArrow_cat C) C (@adjunction_image_func C (@additive_preadditive C
  Prod t Add) t (@additive_terminal_object C Prod t Add) T0 P Q) (@zero_arrow_family_incoming_func K C t
  (@additive_terminal_object C Prod t Add) (@kernel_adjunction_family_func K C (@additive_preadditive C Prod t
  Add) t (@additive_terminal_object C Prod t Add) P (@one_cat_native_snake_alpha_diagram K C
  (@additive_preadditive C Prod t Add) C1 t (@additive_terminal_object C Prod t Add) T0 P A B X D b c h))
  (@transf_arrow_diagram_func K C (@kernel_adjunction_family_func K C (@additive_preadditive C Prod t Add) t
  (@additive_terminal_object C Prod t Add) P (@transf_arrow_diagram_func K C B X b))
  (@kernel_adjunction_family_func K C (@additive_preadditive C Prod t Add) t (@additive_terminal_object C Prod t
  Add) P (@one_cat_native_snake_gamma_diagram K C (@additive_preadditive C Prod t Add) C1 t
  (@additive_terminal_object C Prod t Add) T0 Q A B X D b c h)) (@one_cat_native_snake_kernel_second K C
  (@additive_preadditive C Prod t Add) C1 t (@additive_terminal_object C Prod t Add) T0 P Q A B X D b c h))
  (@one_cat_native_snake_first_exact_input K C C1 Prod t Add T0 P Q N A B X D b c h)))
  (@kernel_adjunction_family_func K C (@additive_preadditive C Prod t Add) t (@additive_terminal_object C Prod t
  Add) P (@transf_arrow_diagram_func K C (@kernel_adjunction_family_func K C (@additive_preadditive C Prod t
  Add) t (@additive_terminal_object C Prod t Add) P (@transf_arrow_diagram_func K C B X b))
  (@kernel_adjunction_family_func K C (@additive_preadditive C Prod t Add) t (@additive_terminal_object C Prod t
  Add) P (@one_cat_native_snake_gamma_diagram K C (@additive_preadditive C Prod t Add) C1 t
  (@additive_terminal_object C Prod t Add) T0 Q A B X D b c h)) (@one_cat_native_snake_kernel_second K C
  (@additive_preadditive C Prod t Add) C1 t (@additive_terminal_object C Prod t Add) T0 P Q A B X D b c h)))
  (@one_cat_native_snake_first_exact_comparison K C C1 Prod t Add T0 P Q N A B X D b c h))) v
  (@one_cat_native_snake_first_kernel_to_image_kernel K C (@additive_preadditive C Prod t Add) C1 t
  (@additive_terminal_object C Prod t Add) T0 P Q A B X D b c h))) _ _
  (@one_cat_native_snake_first_cokernel_after_retraction_zero K C C1 Prod t Add T0 P Q N A B X D b c h))
  (@one_cat_zero_family_precompose_path K C C1 t (@additive_terminal_object C Prod t Add) T0
  (@kernel_adjunction_family_func K C (@additive_preadditive C Prod t Add) t (@additive_terminal_object C Prod t
  Add) P (@transf_arrow_diagram_func K C (@kernel_adjunction_family_func K C (@additive_preadditive C Prod t
  Add) t (@additive_terminal_object C Prod t Add) P (@transf_arrow_diagram_func K C B X b))
  (@kernel_adjunction_family_func K C (@additive_preadditive C Prod t Add) t (@additive_terminal_object C Prod t
  Add) P (@one_cat_native_snake_gamma_diagram K C (@additive_preadditive C Prod t Add) C1 t
  (@additive_terminal_object C Prod t Add) T0 Q A B X D b c h)) (@one_cat_native_snake_kernel_second K C
  (@additive_preadditive C Prod t Add) C1 t (@additive_terminal_object C Prod t Add) T0 P Q A B X D b c h)))
  (@kernel_adjunction_family_func K C (@additive_preadditive C Prod t Add) t (@additive_terminal_object C Prod t
  Add) P (@transf_arrow_diagram_func K C (@one_cat_native_snake_image_func K C (@additive_preadditive C Prod t
  Add) C1 t (@additive_terminal_object C Prod t Add) T0 P Q A B X D b c h) (@kernel_adjunction_family_func K C
  (@additive_preadditive C Prod t Add) t (@additive_terminal_object C Prod t Add) P (@transf_arrow_diagram_func
  K C X D c)) (@one_cat_native_snake_image_lift K C (@additive_preadditive C Prod t Add) C1 t
  (@additive_terminal_object C Prod t Add) T0 P Q A B X D b c h))) (@cokernel_adjunction_family_func K C
  (@additive_preadditive C Prod t Add) t T0 Q (@transf_arrow_diagram_func K C (@comp_cat_fapp0 K (Functor_cat
  WalkingArrow_cat C) C (@adjunction_image_func C (@additive_preadditive C Prod t Add) t
  (@additive_terminal_object C Prod t Add) T0 P Q) (@zero_arrow_family_incoming_func K C t
  (@additive_terminal_object C Prod t Add) (@kernel_adjunction_family_func K C (@additive_preadditive C Prod t
  Add) t (@additive_terminal_object C Prod t Add) P (@one_cat_native_snake_alpha_diagram K C
  (@additive_preadditive C Prod t Add) C1 t (@additive_terminal_object C Prod t Add) T0 P A B X D b c h))
  (@transf_arrow_diagram_func K C (@kernel_adjunction_family_func K C (@additive_preadditive C Prod t Add) t
  (@additive_terminal_object C Prod t Add) P (@transf_arrow_diagram_func K C B X b))
  (@kernel_adjunction_family_func K C (@additive_preadditive C Prod t Add) t (@additive_terminal_object C Prod t
  Add) P (@one_cat_native_snake_gamma_diagram K C (@additive_preadditive C Prod t Add) C1 t
  (@additive_terminal_object C Prod t Add) T0 Q A B X D b c h)) (@one_cat_native_snake_kernel_second K C
  (@additive_preadditive C Prod t Add) C1 t (@additive_terminal_object C Prod t Add) T0 P Q A B X D b c h))
  (@one_cat_native_snake_first_exact_input K C C1 Prod t Add T0 P Q N A B X D b c h)))
  (@kernel_adjunction_family_func K C (@additive_preadditive C Prod t Add) t (@additive_terminal_object C Prod t
  Add) P (@transf_arrow_diagram_func K C (@kernel_adjunction_family_func K C (@additive_preadditive C Prod t
  Add) t (@additive_terminal_object C Prod t Add) P (@transf_arrow_diagram_func K C B X b))
  (@kernel_adjunction_family_func K C (@additive_preadditive C Prod t Add) t (@additive_terminal_object C Prod t
  Add) P (@one_cat_native_snake_gamma_diagram K C (@additive_preadditive C Prod t Add) C1 t
  (@additive_terminal_object C Prod t Add) T0 Q A B X D b c h)) (@one_cat_native_snake_kernel_second K C
  (@additive_preadditive C Prod t Add) C1 t (@additive_terminal_object C Prod t Add) T0 P Q A B X D b c h)))
  (@one_cat_native_snake_first_exact_comparison K C C1 Prod t Add T0 P Q N A B X D b c h)))
  (@one_cat_native_snake_first_kernel_to_image_kernel K C (@additive_preadditive C Prod t Add) C1 t
  (@additive_terminal_object C Prod t Add) T0 P Q A B X D b c h)))));

// Both original zero projections give ΩAlong on the actual first comparison.
symbol one_cat_native_snake_first_exact [K C : Cat]
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
  : τ (@OneCatNativeSnakeFirstExactness K C C1 Prod t Add T0 P Q N A B X D b c h)
≔ (@one_cat_zero_kernel_cokernel_omega K C (@additive_preadditive C Prod t Add) C1 t (@additive_terminal_object
  C Prod t Add) T0 P Q (@transf_arrow_diagram_func K C (@comp_cat_fapp0 K (Functor_cat WalkingArrow_cat C) C
  (@adjunction_image_func C (@additive_preadditive C Prod t Add) t (@additive_terminal_object C Prod t Add) T0 P
  Q) (@zero_arrow_family_incoming_func K C t (@additive_terminal_object C Prod t Add)
  (@kernel_adjunction_family_func K C (@additive_preadditive C Prod t Add) t (@additive_terminal_object C Prod t
  Add) P (@one_cat_native_snake_alpha_diagram K C (@additive_preadditive C Prod t Add) C1 t
  (@additive_terminal_object C Prod t Add) T0 P A B X D b c h)) (@transf_arrow_diagram_func K C
  (@kernel_adjunction_family_func K C (@additive_preadditive C Prod t Add) t (@additive_terminal_object C Prod t
  Add) P (@transf_arrow_diagram_func K C B X b)) (@kernel_adjunction_family_func K C (@additive_preadditive C
  Prod t Add) t (@additive_terminal_object C Prod t Add) P (@one_cat_native_snake_gamma_diagram K C
  (@additive_preadditive C Prod t Add) C1 t (@additive_terminal_object C Prod t Add) T0 Q A B X D b c h))
  (@one_cat_native_snake_kernel_second K C (@additive_preadditive C Prod t Add) C1 t (@additive_terminal_object
  C Prod t Add) T0 P Q A B X D b c h)) (@one_cat_native_snake_first_exact_input K C C1 Prod t Add T0 P Q N A B X
  D b c h))) (@kernel_adjunction_family_func K C (@additive_preadditive C Prod t Add) t
  (@additive_terminal_object C Prod t Add) P (@transf_arrow_diagram_func K C (@kernel_adjunction_family_func K C
  (@additive_preadditive C Prod t Add) t (@additive_terminal_object C Prod t Add) P (@transf_arrow_diagram_func
  K C B X b)) (@kernel_adjunction_family_func K C (@additive_preadditive C Prod t Add) t
  (@additive_terminal_object C Prod t Add) P (@one_cat_native_snake_gamma_diagram K C (@additive_preadditive C
  Prod t Add) C1 t (@additive_terminal_object C Prod t Add) T0 Q A B X D b c h))
  (@one_cat_native_snake_kernel_second K C (@additive_preadditive C Prod t Add) C1 t (@additive_terminal_object
  C Prod t Add) T0 P Q A B X D b c h))) (@one_cat_native_snake_first_exact_comparison K C C1 Prod t Add T0 P Q N
  A B X D b c h)) N (@one_cat_native_snake_first_comparison_kernel_zero K C C1 Prod t Add T0 P Q N A B X D b c
  h) (@one_cat_native_snake_first_comparison_cokernel_zero K C C1 Prod t Add T0 P Q N A B X D b c h));
