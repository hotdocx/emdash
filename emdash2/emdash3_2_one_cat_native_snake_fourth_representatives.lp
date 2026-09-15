/* Corrected whole representatives for the fourth canonical snake comparison. */
require open emdash.emdash3_2_one_cat_native_snake_fourth_covers;
require open emdash.emdash3_2_one_cat_additive_family_units;

// The original source-image factor and both projections reconstruct γx=cps.
symbol one_cat_native_snake_fourth_gamma_representative_path [K C : Cat]
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
  : τ (@= (@Transf K C (@one_cat_native_snake_fourth_gamma_cover_source K C C1 Prod t Add T0 P Q N A B X D b c
  h) D) (@comp_fapp0 (Functor_cat K C) (@one_cat_native_snake_fourth_gamma_cover_source K C C1 Prod t Add T0 P Q
  N A B X D b c h) (@cokernel_adjunction_family_func K C (@additive_preadditive C Prod t Add) t T0 Q
  (@native_snake_incoming_diagram K C t (@additive_terminal_object C Prod t Add) A B X D b c h)) D
  (@one_cat_native_snake_gamma K C (@additive_preadditive C Prod t Add) C1 t (@additive_terminal_object C Prod t
  Add) T0 Q A B X D b c h) (@one_cat_native_snake_fourth_gamma_cover_second K C C1 Prod t Add T0 P Q N A B X D b
  c h)) (@comp_fapp0 (Functor_cat K C) (@one_cat_native_snake_fourth_gamma_cover_source K C C1 Prod t Add T0 P Q
  N A B X D b c h) X D c (@comp_fapp0 (Functor_cat K C) (@one_cat_native_snake_fourth_gamma_cover_source K C C1
  Prod t Add T0 P Q N A B X D b c h) (@one_cat_native_snake_fourth_cover_source K C C1 Prod t Add T0 P Q N A B X
  D b c h) X (@one_cat_native_snake_fourth_cover_lift K C C1 Prod t Add T0 P Q N A B X D b c h)
  (@one_cat_native_snake_fourth_gamma_cover_first K C C1 Prod t Add T0 P Q N A B X D b c h))))
≔ (@eq_trans _ _ _ _ (@eq_ap (@Transf K C (@cokernel_adjunction_family_func K C (@additive_preadditive C Prod t
  Add) t T0 Q (@native_snake_incoming_diagram K C t (@additive_terminal_object C Prod t Add) A B X D b c h)) D)
  (@Transf K C (@one_cat_native_snake_fourth_gamma_cover_source K C C1 Prod t Add T0 P Q N A B X D b c h) D) (λ
  v : τ (@Transf K C (@cokernel_adjunction_family_func K C (@additive_preadditive C Prod t Add) t T0 Q
  (@native_snake_incoming_diagram K C t (@additive_terminal_object C Prod t Add) A B X D b c h)) D),
  (@comp_fapp0 (Functor_cat K C) (@one_cat_native_snake_fourth_gamma_cover_source K C C1 Prod t Add T0 P Q N A B
  X D b c h) (@cokernel_adjunction_family_func K C (@additive_preadditive C Prod t Add) t T0 Q
  (@native_snake_incoming_diagram K C t (@additive_terminal_object C Prod t Add) A B X D b c h)) D v
  (@one_cat_native_snake_fourth_gamma_cover_second K C C1 Prod t Add T0 P Q N A B X D b c h))) _ _ (@eq_sym _ _
  _ (@one_cat_image_family_source_factor_path K C (@additive_preadditive C Prod t Add) C1 t
  (@additive_terminal_object C Prod t Add) T0 P Q (@one_cat_native_snake_gamma_diagram K C
  (@additive_preadditive C Prod t Add) C1 t (@additive_terminal_object C Prod t Add) T0 Q A B X D b c h))))
  (@eq_trans _ _ _ _ (@eq_sym _ _ _ (@comp_assoc (Functor_cat K C)
  (@one_cat_native_snake_fourth_gamma_cover_source K C C1 Prod t Add T0 P Q N A B X D b c h)
  (@cokernel_adjunction_family_func K C (@additive_preadditive C Prod t Add) t T0 Q
  (@native_snake_incoming_diagram K C t (@additive_terminal_object C Prod t Add) A B X D b c h))
  (@comp_cat_fapp0 K (Functor_cat WalkingArrow_cat C) C (@adjunction_image_func C (@additive_preadditive C Prod
  t Add) t (@additive_terminal_object C Prod t Add) T0 P Q) (@one_cat_native_snake_gamma_diagram K C
  (@additive_preadditive C Prod t Add) C1 t (@additive_terminal_object C Prod t Add) T0 Q A B X D b c h)) D
  (@kernel_adjunction_family_inclusion_transf K C (@additive_preadditive C Prod t Add) t
  (@additive_terminal_object C Prod t Add) P (@comp_cat_fapp0 K (Functor_cat WalkingArrow_cat C) (Functor_cat
  WalkingArrow_cat C) (@cokernel_adjunction_arrow_func C (@additive_preadditive C Prod t Add) t T0 Q)
  (@one_cat_native_snake_gamma_diagram K C (@additive_preadditive C Prod t Add) C1 t (@additive_terminal_object
  C Prod t Add) T0 Q A B X D b c h))) (@one_cat_image_family_source_transf K C (@additive_preadditive C Prod t
  Add) C1 t (@additive_terminal_object C Prod t Add) T0 P Q (@one_cat_native_snake_gamma_diagram K C
  (@additive_preadditive C Prod t Add) C1 t (@additive_terminal_object C Prod t Add) T0 Q A B X D b c h))
  (@one_cat_native_snake_fourth_gamma_cover_second K C C1 Prod t Add T0 P Q N A B X D b c h))) (@eq_trans _ _ _
  _ (@eq_ap (@Transf K C (@one_cat_native_snake_fourth_gamma_cover_source K C C1 Prod t Add T0 P Q N A B X D b c
  h) (@comp_cat_fapp0 K (Functor_cat WalkingArrow_cat C) C (@adjunction_image_func C (@additive_preadditive C
  Prod t Add) t (@additive_terminal_object C Prod t Add) T0 P Q) (@one_cat_native_snake_gamma_diagram K C
  (@additive_preadditive C Prod t Add) C1 t (@additive_terminal_object C Prod t Add) T0 Q A B X D b c h)))
  (@Transf K C (@one_cat_native_snake_fourth_gamma_cover_source K C C1 Prod t Add T0 P Q N A B X D b c h) D) (λ
  v : τ (@Transf K C (@one_cat_native_snake_fourth_gamma_cover_source K C C1 Prod t Add T0 P Q N A B X D b c h)
  (@comp_cat_fapp0 K (Functor_cat WalkingArrow_cat C) C (@adjunction_image_func C (@additive_preadditive C Prod
  t Add) t (@additive_terminal_object C Prod t Add) T0 P Q) (@one_cat_native_snake_gamma_diagram K C
  (@additive_preadditive C Prod t Add) C1 t (@additive_terminal_object C Prod t Add) T0 Q A B X D b c h))),
  (@comp_fapp0 (Functor_cat K C) (@one_cat_native_snake_fourth_gamma_cover_source K C C1 Prod t Add T0 P Q N A B
  X D b c h) (@comp_cat_fapp0 K (Functor_cat WalkingArrow_cat C) C (@adjunction_image_func C
  (@additive_preadditive C Prod t Add) t (@additive_terminal_object C Prod t Add) T0 P Q)
  (@one_cat_native_snake_gamma_diagram K C (@additive_preadditive C Prod t Add) C1 t (@additive_terminal_object
  C Prod t Add) T0 Q A B X D b c h)) D (@kernel_adjunction_family_inclusion_transf K C (@additive_preadditive C
  Prod t Add) t (@additive_terminal_object C Prod t Add) P (@comp_cat_fapp0 K (Functor_cat WalkingArrow_cat C)
  (Functor_cat WalkingArrow_cat C) (@cokernel_adjunction_arrow_func C (@additive_preadditive C Prod t Add) t T0
  Q) (@one_cat_native_snake_gamma_diagram K C (@additive_preadditive C Prod t Add) C1 t
  (@additive_terminal_object C Prod t Add) T0 Q A B X D b c h))) v)) _ _ (@eq_sym _ _ _
  (@one_cat_native_snake_fourth_gamma_cover_compatibility K C C1 Prod t Add T0 P Q N A B X D b c h))) (@eq_trans
  _ _ _ _ (@comp_assoc (Functor_cat K C) (@one_cat_native_snake_fourth_gamma_cover_source K C C1 Prod t Add T0 P
  Q N A B X D b c h) (@one_cat_native_snake_fourth_cover_source K C C1 Prod t Add T0 P Q N A B X D b c h)
  (@comp_cat_fapp0 K (Functor_cat WalkingArrow_cat C) C (@adjunction_image_func C (@additive_preadditive C Prod
  t Add) t (@additive_terminal_object C Prod t Add) T0 P Q) (@one_cat_native_snake_gamma_diagram K C
  (@additive_preadditive C Prod t Add) C1 t (@additive_terminal_object C Prod t Add) T0 Q A B X D b c h)) D
  (@kernel_adjunction_family_inclusion_transf K C (@additive_preadditive C Prod t Add) t
  (@additive_terminal_object C Prod t Add) P (@comp_cat_fapp0 K (Functor_cat WalkingArrow_cat C) (Functor_cat
  WalkingArrow_cat C) (@cokernel_adjunction_arrow_func C (@additive_preadditive C Prod t Add) t T0 Q)
  (@one_cat_native_snake_gamma_diagram K C (@additive_preadditive C Prod t Add) C1 t (@additive_terminal_object
  C Prod t Add) T0 Q A B X D b c h))) (@one_cat_native_snake_fourth_cover_image_lift K C C1 Prod t Add T0 P Q N
  A B X D b c h) (@one_cat_native_snake_fourth_gamma_cover_first K C C1 Prod t Add T0 P Q N A B X D b c h))
  (@eq_trans _ _ _ _ (@eq_ap (@Transf K C (@one_cat_native_snake_fourth_cover_source K C C1 Prod t Add T0 P Q N
  A B X D b c h) D) (@Transf K C (@one_cat_native_snake_fourth_gamma_cover_source K C C1 Prod t Add T0 P Q N A B
  X D b c h) D) (λ v : τ (@Transf K C (@one_cat_native_snake_fourth_cover_source K C C1 Prod t Add T0 P Q N A B
  X D b c h) D), (@comp_fapp0 (Functor_cat K C) (@one_cat_native_snake_fourth_gamma_cover_source K C C1 Prod t
  Add T0 P Q N A B X D b c h) (@one_cat_native_snake_fourth_cover_source K C C1 Prod t Add T0 P Q N A B X D b c
  h) D v (@one_cat_native_snake_fourth_gamma_cover_first K C C1 Prod t Add T0 P Q N A B X D b c h))) _ _
  (@one_cat_native_snake_fourth_cover_image_reconstruction K C C1 Prod t Add T0 P Q N A B X D b c h)) (@eq_sym _
  _ _ (@comp_assoc (Functor_cat K C) (@one_cat_native_snake_fourth_gamma_cover_source K C C1 Prod t Add T0 P Q N
  A B X D b c h) (@one_cat_native_snake_fourth_cover_source K C C1 Prod t Add T0 P Q N A B X D b c h) X D c
  (@one_cat_native_snake_fourth_cover_lift K C C1 Prod t Add T0 P Q N A B X D b c h)
  (@one_cat_native_snake_fourth_gamma_cover_first K C C1 Prod t Add T0 P Q N A B X D b c h))))))));

// The original whole difference psu−by corrects the X representative.
symbol one_cat_native_snake_fourth_difference [K C : Cat]
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
  : τ (@Transf K C (@one_cat_native_snake_fourth_quotient_cover_source K C C1 Prod t Add T0 P Q N A B X D b c h)
  X)
≔ (@one_cat_difference_family K C C1 Prod t Add T0 (@one_cat_native_snake_fourth_quotient_cover_source K C C1
  Prod t Add T0 P Q N A B X D b c h) X (@comp_fapp0 (Functor_cat K C)
  (@one_cat_native_snake_fourth_quotient_cover_source K C C1 Prod t Add T0 P Q N A B X D b c h)
  (@one_cat_native_snake_fourth_gamma_cover_source K C C1 Prod t Add T0 P Q N A B X D b c h) X (@comp_fapp0
  (Functor_cat K C) (@one_cat_native_snake_fourth_gamma_cover_source K C C1 Prod t Add T0 P Q N A B X D b c h)
  (@one_cat_native_snake_fourth_cover_source K C C1 Prod t Add T0 P Q N A B X D b c h) X
  (@one_cat_native_snake_fourth_cover_lift K C C1 Prod t Add T0 P Q N A B X D b c h)
  (@one_cat_native_snake_fourth_gamma_cover_first K C C1 Prod t Add T0 P Q N A B X D b c h))
  (@one_cat_native_snake_fourth_quotient_cover_first K C C1 Prod t Add T0 P Q N A B X D b c h)) (@comp_fapp0
  (Functor_cat K C) (@one_cat_native_snake_fourth_quotient_cover_source K C C1 Prod t Add T0 P Q N A B X D b c
  h) B X b (@one_cat_native_snake_fourth_quotient_cover_second K C C1 Prod t Add T0 P Q N A B X D b c h)));

// Whole bilinearity and the original γπ_a=cb give c(psu−by)=0.
symbol one_cat_native_snake_fourth_difference_zero [K C : Cat]
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
  : τ (@= (@Transf K C (@one_cat_native_snake_fourth_quotient_cover_source K C C1 Prod t Add T0 P Q N A B X D b
  c h) D) (@comp_fapp0 (Functor_cat K C) (@one_cat_native_snake_fourth_quotient_cover_source K C C1 Prod t Add
  T0 P Q N A B X D b c h) X D c (@one_cat_native_snake_fourth_difference K C C1 Prod t Add T0 P Q N A B X D b c
  h)) (@zero_arrow_family_zero_transf K C t (@additive_terminal_object C Prod t Add) T0
  (@one_cat_native_snake_fourth_quotient_cover_source K C C1 Prod t Add T0 P Q N A B X D b c h) D))
≔ (@one_cat_difference_family_postcompose_zero_path K C C1 Prod t Add T0
  (@one_cat_native_snake_fourth_quotient_cover_source K C C1 Prod t Add T0 P Q N A B X D b c h) X D (@comp_fapp0
  (Functor_cat K C) (@one_cat_native_snake_fourth_quotient_cover_source K C C1 Prod t Add T0 P Q N A B X D b c
  h) (@one_cat_native_snake_fourth_gamma_cover_source K C C1 Prod t Add T0 P Q N A B X D b c h) X (@comp_fapp0
  (Functor_cat K C) (@one_cat_native_snake_fourth_gamma_cover_source K C C1 Prod t Add T0 P Q N A B X D b c h)
  (@one_cat_native_snake_fourth_cover_source K C C1 Prod t Add T0 P Q N A B X D b c h) X
  (@one_cat_native_snake_fourth_cover_lift K C C1 Prod t Add T0 P Q N A B X D b c h)
  (@one_cat_native_snake_fourth_gamma_cover_first K C C1 Prod t Add T0 P Q N A B X D b c h))
  (@one_cat_native_snake_fourth_quotient_cover_first K C C1 Prod t Add T0 P Q N A B X D b c h)) (@comp_fapp0
  (Functor_cat K C) (@one_cat_native_snake_fourth_quotient_cover_source K C C1 Prod t Add T0 P Q N A B X D b c
  h) B X b (@one_cat_native_snake_fourth_quotient_cover_second K C C1 Prod t Add T0 P Q N A B X D b c h)) c
  (@eq_trans _ _ _ _ (@comp_assoc (Functor_cat K C) (@one_cat_native_snake_fourth_quotient_cover_source K C C1
  Prod t Add T0 P Q N A B X D b c h) (@one_cat_native_snake_fourth_gamma_cover_source K C C1 Prod t Add T0 P Q N
  A B X D b c h) X D c (@comp_fapp0 (Functor_cat K C) (@one_cat_native_snake_fourth_gamma_cover_source K C C1
  Prod t Add T0 P Q N A B X D b c h) (@one_cat_native_snake_fourth_cover_source K C C1 Prod t Add T0 P Q N A B X
  D b c h) X (@one_cat_native_snake_fourth_cover_lift K C C1 Prod t Add T0 P Q N A B X D b c h)
  (@one_cat_native_snake_fourth_gamma_cover_first K C C1 Prod t Add T0 P Q N A B X D b c h))
  (@one_cat_native_snake_fourth_quotient_cover_first K C C1 Prod t Add T0 P Q N A B X D b c h)) (@eq_trans _ _ _
  _ (@eq_ap (@Transf K C (@one_cat_native_snake_fourth_gamma_cover_source K C C1 Prod t Add T0 P Q N A B X D b c
  h) D) (@Transf K C (@one_cat_native_snake_fourth_quotient_cover_source K C C1 Prod t Add T0 P Q N A B X D b c
  h) D) (λ v : τ (@Transf K C (@one_cat_native_snake_fourth_gamma_cover_source K C C1 Prod t Add T0 P Q N A B X
  D b c h) D), (@comp_fapp0 (Functor_cat K C) (@one_cat_native_snake_fourth_quotient_cover_source K C C1 Prod t
  Add T0 P Q N A B X D b c h) (@one_cat_native_snake_fourth_gamma_cover_source K C C1 Prod t Add T0 P Q N A B X
  D b c h) D v (@one_cat_native_snake_fourth_quotient_cover_first K C C1 Prod t Add T0 P Q N A B X D b c h))) _
  _ (@eq_sym _ _ _ (@one_cat_native_snake_fourth_gamma_representative_path K C C1 Prod t Add T0 P Q N A B X D b
  c h))) (@eq_trans _ _ _ _ (@eq_sym _ _ _ (@comp_assoc (Functor_cat K C)
  (@one_cat_native_snake_fourth_quotient_cover_source K C C1 Prod t Add T0 P Q N A B X D b c h)
  (@one_cat_native_snake_fourth_gamma_cover_source K C C1 Prod t Add T0 P Q N A B X D b c h)
  (@cokernel_adjunction_family_func K C (@additive_preadditive C Prod t Add) t T0 Q
  (@native_snake_incoming_diagram K C t (@additive_terminal_object C Prod t Add) A B X D b c h)) D
  (@one_cat_native_snake_gamma K C (@additive_preadditive C Prod t Add) C1 t (@additive_terminal_object C Prod t
  Add) T0 Q A B X D b c h) (@one_cat_native_snake_fourth_gamma_cover_second K C C1 Prod t Add T0 P Q N A B X D b
  c h) (@one_cat_native_snake_fourth_quotient_cover_first K C C1 Prod t Add T0 P Q N A B X D b c h))) (@eq_trans
  _ _ _ _ (@eq_ap (@Transf K C (@one_cat_native_snake_fourth_quotient_cover_source K C C1 Prod t Add T0 P Q N A
  B X D b c h) (@cokernel_adjunction_family_func K C (@additive_preadditive C Prod t Add) t T0 Q
  (@native_snake_incoming_diagram K C t (@additive_terminal_object C Prod t Add) A B X D b c h))) (@Transf K C
  (@one_cat_native_snake_fourth_quotient_cover_source K C C1 Prod t Add T0 P Q N A B X D b c h) D) (λ v : τ
  (@Transf K C (@one_cat_native_snake_fourth_quotient_cover_source K C C1 Prod t Add T0 P Q N A B X D b c h)
  (@cokernel_adjunction_family_func K C (@additive_preadditive C Prod t Add) t T0 Q
  (@native_snake_incoming_diagram K C t (@additive_terminal_object C Prod t Add) A B X D b c h))), (@comp_fapp0
  (Functor_cat K C) (@one_cat_native_snake_fourth_quotient_cover_source K C C1 Prod t Add T0 P Q N A B X D b c
  h) (@cokernel_adjunction_family_func K C (@additive_preadditive C Prod t Add) t T0 Q
  (@native_snake_incoming_diagram K C t (@additive_terminal_object C Prod t Add) A B X D b c h)) D
  (@one_cat_native_snake_gamma K C (@additive_preadditive C Prod t Add) C1 t (@additive_terminal_object C Prod t
  Add) T0 Q A B X D b c h) v)) _ _ (@one_cat_native_snake_fourth_quotient_cover_compatibility K C C1 Prod t Add
  T0 P Q N A B X D b c h)) (@eq_trans _ _ _ _ (@comp_assoc (Functor_cat K C)
  (@one_cat_native_snake_fourth_quotient_cover_source K C C1 Prod t Add T0 P Q N A B X D b c h) B
  (@cokernel_adjunction_family_func K C (@additive_preadditive C Prod t Add) t T0 Q
  (@native_snake_incoming_diagram K C t (@additive_terminal_object C Prod t Add) A B X D b c h)) D
  (@one_cat_native_snake_gamma K C (@additive_preadditive C Prod t Add) C1 t (@additive_terminal_object C Prod t
  Add) T0 Q A B X D b c h) (@cokernel_adjunction_family_projection_transf K C (@additive_preadditive C Prod t
  Add) t T0 Q (@native_snake_incoming_diagram K C t (@additive_terminal_object C Prod t Add) A B X D b c h))
  (@one_cat_native_snake_fourth_quotient_cover_second K C C1 Prod t Add T0 P Q N A B X D b c h)) (@eq_trans _ _
  _ _ (@eq_ap (@Transf K C B D) (@Transf K C (@one_cat_native_snake_fourth_quotient_cover_source K C C1 Prod t
  Add T0 P Q N A B X D b c h) D) (λ v : τ (@Transf K C B D), (@comp_fapp0 (Functor_cat K C)
  (@one_cat_native_snake_fourth_quotient_cover_source K C C1 Prod t Add T0 P Q N A B X D b c h) B D v
  (@one_cat_native_snake_fourth_quotient_cover_second K C C1 Prod t Add T0 P Q N A B X D b c h))) _ _
  (@one_cat_native_snake_gamma_reconstruction K C (@additive_preadditive C Prod t Add) C1 t
  (@additive_terminal_object C Prod t Add) T0 Q A B X D b c h)) (@eq_sym _ _ _ (@comp_assoc (Functor_cat K C)
  (@one_cat_native_snake_fourth_quotient_cover_source K C C1 Prod t Add T0 P Q N A B X D b c h) B X D c b
  (@one_cat_native_snake_fourth_quotient_cover_second K C C1 Prod t Add T0 P Q N A B X D b c h))))))))));

// The original native kernel mate lifts the difference into K(c).
symbol one_cat_native_snake_fourth_kernel_lift [K C : Cat]
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
  : τ (@Transf K C (@one_cat_native_snake_fourth_quotient_cover_source K C C1 Prod t Add T0 P Q N A B X D b c h)
  (@kernel_adjunction_family_func K C (@additive_preadditive C Prod t Add) t (@additive_terminal_object C Prod t
  Add) P (@transf_arrow_diagram_func K C X D c)))
≔ (@one_cat_kernel_family_lift K C (@additive_preadditive C Prod t Add) C1 t (@additive_terminal_object C Prod t
  Add) T0 P (@one_cat_native_snake_fourth_quotient_cover_source K C C1 Prod t Add T0 P Q N A B X D b c h)
  (@transf_arrow_diagram_func K C X D c) (@one_cat_native_snake_fourth_difference K C C1 Prod t Add T0 P Q N A B
  X D b c h) (@one_cat_native_snake_fourth_difference_zero K C C1 Prod t Add T0 P Q N A B X D b c h));

// The original κ_c reconstructs that same whole difference.
symbol one_cat_native_snake_fourth_kernel_reconstruction [K C : Cat]
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
  : τ (@= (@Transf K C (@one_cat_native_snake_fourth_quotient_cover_source K C C1 Prod t Add T0 P Q N A B X D b
  c h) X) (@comp_fapp0 (Functor_cat K C) (@one_cat_native_snake_fourth_quotient_cover_source K C C1 Prod t Add
  T0 P Q N A B X D b c h) (@kernel_adjunction_family_func K C (@additive_preadditive C Prod t Add) t
  (@additive_terminal_object C Prod t Add) P (@transf_arrow_diagram_func K C X D c)) X
  (@kernel_adjunction_family_inclusion_transf K C (@additive_preadditive C Prod t Add) t
  (@additive_terminal_object C Prod t Add) P (@transf_arrow_diagram_func K C X D c))
  (@one_cat_native_snake_fourth_kernel_lift K C C1 Prod t Add T0 P Q N A B X D b c h))
  (@one_cat_native_snake_fourth_difference K C C1 Prod t Add T0 P Q N A B X D b c h))
≔ (@one_cat_kernel_family_lift_ambient_reconstruction K C (@additive_preadditive C Prod t Add) C1 t
  (@additive_terminal_object C Prod t Add) T0 P (@one_cat_native_snake_fourth_quotient_cover_source K C C1 Prod
  t Add T0 P Q N A B X D b c h) (@transf_arrow_diagram_func K C X D c) (@one_cat_native_snake_fourth_difference
  K C C1 Prod t Add T0 P Q N A B X D b c h) (@one_cat_native_snake_fourth_difference_zero K C C1 Prod t Add T0 P
  Q N A B X D b c h));

// The original π_b kills by and retains psu after subtraction.
symbol one_cat_native_snake_fourth_difference_quotient_path [K C : Cat]
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
  : τ (@= (@Transf K C (@one_cat_native_snake_fourth_quotient_cover_source K C C1 Prod t Add T0 P Q N A B X D b
  c h) (@cokernel_adjunction_family_func K C (@additive_preadditive C Prod t Add) t T0 Q
  (@transf_arrow_diagram_func K C B X b))) (@comp_fapp0 (Functor_cat K C)
  (@one_cat_native_snake_fourth_quotient_cover_source K C C1 Prod t Add T0 P Q N A B X D b c h) X
  (@cokernel_adjunction_family_func K C (@additive_preadditive C Prod t Add) t T0 Q (@transf_arrow_diagram_func
  K C B X b)) (@cokernel_adjunction_family_projection_transf K C (@additive_preadditive C Prod t Add) t T0 Q
  (@transf_arrow_diagram_func K C B X b)) (@one_cat_native_snake_fourth_difference K C C1 Prod t Add T0 P Q N A
  B X D b c h)) (@comp_fapp0 (Functor_cat K C) (@one_cat_native_snake_fourth_quotient_cover_source K C C1 Prod t
  Add T0 P Q N A B X D b c h) X (@cokernel_adjunction_family_func K C (@additive_preadditive C Prod t Add) t T0
  Q (@transf_arrow_diagram_func K C B X b)) (@cokernel_adjunction_family_projection_transf K C
  (@additive_preadditive C Prod t Add) t T0 Q (@transf_arrow_diagram_func K C B X b)) (@comp_fapp0 (Functor_cat
  K C) (@one_cat_native_snake_fourth_quotient_cover_source K C C1 Prod t Add T0 P Q N A B X D b c h)
  (@one_cat_native_snake_fourth_gamma_cover_source K C C1 Prod t Add T0 P Q N A B X D b c h) X (@comp_fapp0
  (Functor_cat K C) (@one_cat_native_snake_fourth_gamma_cover_source K C C1 Prod t Add T0 P Q N A B X D b c h)
  (@one_cat_native_snake_fourth_cover_source K C C1 Prod t Add T0 P Q N A B X D b c h) X
  (@one_cat_native_snake_fourth_cover_lift K C C1 Prod t Add T0 P Q N A B X D b c h)
  (@one_cat_native_snake_fourth_gamma_cover_first K C C1 Prod t Add T0 P Q N A B X D b c h))
  (@one_cat_native_snake_fourth_quotient_cover_first K C C1 Prod t Add T0 P Q N A B X D b c h))))
≔ (@one_cat_difference_killed_second_path K C C1 Prod t Add T0
  (@one_cat_native_snake_fourth_quotient_cover_source K C C1 Prod t Add T0 P Q N A B X D b c h) X
  (@cokernel_adjunction_family_func K C (@additive_preadditive C Prod t Add) t T0 Q (@transf_arrow_diagram_func
  K C B X b)) (@comp_fapp0 (Functor_cat K C) (@one_cat_native_snake_fourth_quotient_cover_source K C C1 Prod t
  Add T0 P Q N A B X D b c h) (@one_cat_native_snake_fourth_gamma_cover_source K C C1 Prod t Add T0 P Q N A B X
  D b c h) X (@comp_fapp0 (Functor_cat K C) (@one_cat_native_snake_fourth_gamma_cover_source K C C1 Prod t Add
  T0 P Q N A B X D b c h) (@one_cat_native_snake_fourth_cover_source K C C1 Prod t Add T0 P Q N A B X D b c h) X
  (@one_cat_native_snake_fourth_cover_lift K C C1 Prod t Add T0 P Q N A B X D b c h)
  (@one_cat_native_snake_fourth_gamma_cover_first K C C1 Prod t Add T0 P Q N A B X D b c h))
  (@one_cat_native_snake_fourth_quotient_cover_first K C C1 Prod t Add T0 P Q N A B X D b c h)) (@comp_fapp0
  (Functor_cat K C) (@one_cat_native_snake_fourth_quotient_cover_source K C C1 Prod t Add T0 P Q N A B X D b c
  h) B X b (@one_cat_native_snake_fourth_quotient_cover_second K C C1 Prod t Add T0 P Q N A B X D b c h))
  (@cokernel_adjunction_family_projection_transf K C (@additive_preadditive C Prod t Add) t T0 Q
  (@transf_arrow_diagram_func K C B X b)) (@eq_trans _ _ _ _ (@comp_assoc (Functor_cat K C)
  (@one_cat_native_snake_fourth_quotient_cover_source K C C1 Prod t Add T0 P Q N A B X D b c h) B X
  (@cokernel_adjunction_family_func K C (@additive_preadditive C Prod t Add) t T0 Q (@transf_arrow_diagram_func
  K C B X b)) (@cokernel_adjunction_family_projection_transf K C (@additive_preadditive C Prod t Add) t T0 Q
  (@transf_arrow_diagram_func K C B X b)) b (@one_cat_native_snake_fourth_quotient_cover_second K C C1 Prod t
  Add T0 P Q N A B X D b c h)) (@eq_trans _ _ _ _ (@eq_ap (@Transf K C B (@cokernel_adjunction_family_func K C
  (@additive_preadditive C Prod t Add) t T0 Q (@transf_arrow_diagram_func K C B X b))) (@Transf K C
  (@one_cat_native_snake_fourth_quotient_cover_source K C C1 Prod t Add T0 P Q N A B X D b c h)
  (@cokernel_adjunction_family_func K C (@additive_preadditive C Prod t Add) t T0 Q (@transf_arrow_diagram_func
  K C B X b))) (λ v : τ (@Transf K C B (@cokernel_adjunction_family_func K C (@additive_preadditive C Prod t
  Add) t T0 Q (@transf_arrow_diagram_func K C B X b))), (@comp_fapp0 (Functor_cat K C)
  (@one_cat_native_snake_fourth_quotient_cover_source K C C1 Prod t Add T0 P Q N A B X D b c h) B
  (@cokernel_adjunction_family_func K C (@additive_preadditive C Prod t Add) t T0 Q (@transf_arrow_diagram_func
  K C B X b)) v (@one_cat_native_snake_fourth_quotient_cover_second K C C1 Prod t Add T0 P Q N A B X D b c h)))
  _ _ (@one_cat_cokernel_family_annihilation_path K C (@additive_preadditive C Prod t Add) C1 t
  (@additive_terminal_object C Prod t Add) T0 Q (@transf_arrow_diagram_func K C B X b)))
  (@one_cat_zero_family_precompose_path K C C1 t (@additive_terminal_object C Prod t Add) T0
  (@one_cat_native_snake_fourth_quotient_cover_source K C C1 Prod t Add T0 P Q N A B X D b c h) B
  (@cokernel_adjunction_family_func K C (@additive_preadditive C Prod t Add) t T0 Q (@transf_arrow_diagram_func
  K C B X b)) (@one_cat_native_snake_fourth_quotient_cover_second K C C1 Prod t Add T0 P Q N A B X D b c h)))));

// The original π_α sends the K(c) lift into Q(α).
symbol one_cat_native_snake_fourth_cokernel_representative [K C : Cat]
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
  : τ (@Transf K C (@one_cat_native_snake_fourth_quotient_cover_source K C C1 Prod t Add T0 P Q N A B X D b c h)
  (@cokernel_adjunction_family_func K C (@additive_preadditive C Prod t Add) t T0 Q
  (@one_cat_native_snake_alpha_diagram K C (@additive_preadditive C Prod t Add) C1 t (@additive_terminal_object
  C Prod t Add) T0 P A B X D b c h)))
≔ (@comp_fapp0 (Functor_cat K C) (@one_cat_native_snake_fourth_quotient_cover_source K C C1 Prod t Add T0 P Q N
  A B X D b c h) (@kernel_adjunction_family_func K C (@additive_preadditive C Prod t Add) t
  (@additive_terminal_object C Prod t Add) P (@transf_arrow_diagram_func K C X D c))
  (@cokernel_adjunction_family_func K C (@additive_preadditive C Prod t Add) t T0 Q
  (@one_cat_native_snake_alpha_diagram K C (@additive_preadditive C Prod t Add) C1 t (@additive_terminal_object
  C Prod t Add) T0 P A B X D b c h)) (@cokernel_adjunction_family_projection_transf K C (@additive_preadditive C
  Prod t Add) t T0 Q (@one_cat_native_snake_alpha_diagram K C (@additive_preadditive C Prod t Add) C1 t
  (@additive_terminal_object C Prod t Add) T0 P A B X D b c h)) (@one_cat_native_snake_fourth_kernel_lift K C C1
  Prod t Add T0 P Q N A B X D b c h));

// The actual q₁ reconstructs μrsu from the same three cover projections.
symbol one_cat_native_snake_fourth_cokernel_representative_path [K C : Cat]
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
  : τ (@= (@Transf K C (@one_cat_native_snake_fourth_quotient_cover_source K C C1 Prod t Add T0 P Q N A B X D b
  c h) (@cokernel_adjunction_family_func K C (@additive_preadditive C Prod t Add) t T0 Q
  (@transf_arrow_diagram_func K C B X b))) (@comp_fapp0 (Functor_cat K C)
  (@one_cat_native_snake_fourth_quotient_cover_source K C C1 Prod t Add T0 P Q N A B X D b c h)
  (@cokernel_adjunction_family_func K C (@additive_preadditive C Prod t Add) t T0 Q
  (@one_cat_native_snake_alpha_diagram K C (@additive_preadditive C Prod t Add) C1 t (@additive_terminal_object
  C Prod t Add) T0 P A B X D b c h)) (@cokernel_adjunction_family_func K C (@additive_preadditive C Prod t Add)
  t T0 Q (@transf_arrow_diagram_func K C B X b)) (@one_cat_native_snake_cokernel_first K C
  (@additive_preadditive C Prod t Add) C1 t (@additive_terminal_object C Prod t Add) T0 P Q A B X D b c h)
  (@one_cat_native_snake_fourth_cokernel_representative K C C1 Prod t Add T0 P Q N A B X D b c h)) (@comp_fapp0
  (Functor_cat K C) (@one_cat_native_snake_fourth_quotient_cover_source K C C1 Prod t Add T0 P Q N A B X D b c
  h) (@kernel_adjunction_family_func K C (@additive_preadditive C Prod t Add) t (@additive_terminal_object C
  Prod t Add) P (@transf_arrow_diagram_func K C (@cokernel_adjunction_family_func K C (@additive_preadditive C
  Prod t Add) t T0 Q (@transf_arrow_diagram_func K C B X b)) (@cokernel_adjunction_family_func K C
  (@additive_preadditive C Prod t Add) t T0 Q (@one_cat_native_snake_gamma_diagram K C (@additive_preadditive C
  Prod t Add) C1 t (@additive_terminal_object C Prod t Add) T0 Q A B X D b c h))
  (@one_cat_native_snake_cokernel_second K C (@additive_preadditive C Prod t Add) C1 t
  (@additive_terminal_object C Prod t Add) T0 P Q A B X D b c h))) (@cokernel_adjunction_family_func K C
  (@additive_preadditive C Prod t Add) t T0 Q (@transf_arrow_diagram_func K C B X b))
  (@kernel_adjunction_family_inclusion_transf K C (@additive_preadditive C Prod t Add) t
  (@additive_terminal_object C Prod t Add) P (@transf_arrow_diagram_func K C (@cokernel_adjunction_family_func K
  C (@additive_preadditive C Prod t Add) t T0 Q (@transf_arrow_diagram_func K C B X b))
  (@cokernel_adjunction_family_func K C (@additive_preadditive C Prod t Add) t T0 Q
  (@one_cat_native_snake_gamma_diagram K C (@additive_preadditive C Prod t Add) C1 t (@additive_terminal_object
  C Prod t Add) T0 Q A B X D b c h)) (@one_cat_native_snake_cokernel_second K C (@additive_preadditive C Prod t
  Add) C1 t (@additive_terminal_object C Prod t Add) T0 P Q A B X D b c h))) (@comp_fapp0 (Functor_cat K C)
  (@one_cat_native_snake_fourth_quotient_cover_source K C C1 Prod t Add T0 P Q N A B X D b c h)
  (@one_cat_native_snake_fourth_gamma_cover_source K C C1 Prod t Add T0 P Q N A B X D b c h)
  (@kernel_adjunction_family_func K C (@additive_preadditive C Prod t Add) t (@additive_terminal_object C Prod t
  Add) P (@transf_arrow_diagram_func K C (@cokernel_adjunction_family_func K C (@additive_preadditive C Prod t
  Add) t T0 Q (@transf_arrow_diagram_func K C B X b)) (@cokernel_adjunction_family_func K C
  (@additive_preadditive C Prod t Add) t T0 Q (@one_cat_native_snake_gamma_diagram K C (@additive_preadditive C
  Prod t Add) C1 t (@additive_terminal_object C Prod t Add) T0 Q A B X D b c h))
  (@one_cat_native_snake_cokernel_second K C (@additive_preadditive C Prod t Add) C1 t
  (@additive_terminal_object C Prod t Add) T0 P Q A B X D b c h))) (@comp_fapp0 (Functor_cat K C)
  (@one_cat_native_snake_fourth_gamma_cover_source K C C1 Prod t Add T0 P Q N A B X D b c h)
  (@one_cat_native_snake_fourth_cover_source K C C1 Prod t Add T0 P Q N A B X D b c h)
  (@kernel_adjunction_family_func K C (@additive_preadditive C Prod t Add) t (@additive_terminal_object C Prod t
  Add) P (@transf_arrow_diagram_func K C (@cokernel_adjunction_family_func K C (@additive_preadditive C Prod t
  Add) t T0 Q (@transf_arrow_diagram_func K C B X b)) (@cokernel_adjunction_family_func K C
  (@additive_preadditive C Prod t Add) t T0 Q (@one_cat_native_snake_gamma_diagram K C (@additive_preadditive C
  Prod t Add) C1 t (@additive_terminal_object C Prod t Add) T0 Q A B X D b c h))
  (@one_cat_native_snake_cokernel_second K C (@additive_preadditive C Prod t Add) C1 t
  (@additive_terminal_object C Prod t Add) T0 P Q A B X D b c h)))
  (@one_cat_native_snake_fourth_cover_projection K C C1 Prod t Add T0 P Q N A B X D b c h)
  (@one_cat_native_snake_fourth_gamma_cover_first K C C1 Prod t Add T0 P Q N A B X D b c h))
  (@one_cat_native_snake_fourth_quotient_cover_first K C C1 Prod t Add T0 P Q N A B X D b c h))))
≔ (@eq_trans _ _ _ _ (@comp_assoc (Functor_cat K C) (@one_cat_native_snake_fourth_quotient_cover_source K C C1
  Prod t Add T0 P Q N A B X D b c h) (@kernel_adjunction_family_func K C (@additive_preadditive C Prod t Add) t
  (@additive_terminal_object C Prod t Add) P (@transf_arrow_diagram_func K C X D c))
  (@cokernel_adjunction_family_func K C (@additive_preadditive C Prod t Add) t T0 Q
  (@one_cat_native_snake_alpha_diagram K C (@additive_preadditive C Prod t Add) C1 t (@additive_terminal_object
  C Prod t Add) T0 P A B X D b c h)) (@cokernel_adjunction_family_func K C (@additive_preadditive C Prod t Add)
  t T0 Q (@transf_arrow_diagram_func K C B X b)) (@one_cat_native_snake_cokernel_first K C
  (@additive_preadditive C Prod t Add) C1 t (@additive_terminal_object C Prod t Add) T0 P Q A B X D b c h)
  (@cokernel_adjunction_family_projection_transf K C (@additive_preadditive C Prod t Add) t T0 Q
  (@one_cat_native_snake_alpha_diagram K C (@additive_preadditive C Prod t Add) C1 t (@additive_terminal_object
  C Prod t Add) T0 P A B X D b c h)) (@one_cat_native_snake_fourth_kernel_lift K C C1 Prod t Add T0 P Q N A B X
  D b c h)) (@eq_trans _ _ _ _ (@eq_ap (@Transf K C (@kernel_adjunction_family_func K C (@additive_preadditive C
  Prod t Add) t (@additive_terminal_object C Prod t Add) P (@transf_arrow_diagram_func K C X D c))
  (@cokernel_adjunction_family_func K C (@additive_preadditive C Prod t Add) t T0 Q (@transf_arrow_diagram_func
  K C B X b))) (@Transf K C (@one_cat_native_snake_fourth_quotient_cover_source K C C1 Prod t Add T0 P Q N A B X
  D b c h) (@cokernel_adjunction_family_func K C (@additive_preadditive C Prod t Add) t T0 Q
  (@transf_arrow_diagram_func K C B X b))) (λ v : τ (@Transf K C (@kernel_adjunction_family_func K C
  (@additive_preadditive C Prod t Add) t (@additive_terminal_object C Prod t Add) P (@transf_arrow_diagram_func
  K C X D c)) (@cokernel_adjunction_family_func K C (@additive_preadditive C Prod t Add) t T0 Q
  (@transf_arrow_diagram_func K C B X b))), (@comp_fapp0 (Functor_cat K C)
  (@one_cat_native_snake_fourth_quotient_cover_source K C C1 Prod t Add T0 P Q N A B X D b c h)
  (@kernel_adjunction_family_func K C (@additive_preadditive C Prod t Add) t (@additive_terminal_object C Prod t
  Add) P (@transf_arrow_diagram_func K C X D c)) (@cokernel_adjunction_family_func K C (@additive_preadditive C
  Prod t Add) t T0 Q (@transf_arrow_diagram_func K C B X b)) v (@one_cat_native_snake_fourth_kernel_lift K C C1
  Prod t Add T0 P Q N A B X D b c h))) _ _ (@one_cat_native_snake_cokernel_first_reconstruction K C
  (@additive_preadditive C Prod t Add) C1 t (@additive_terminal_object C Prod t Add) T0 P Q A B X D b c h))
  (@eq_trans _ _ _ _ (@eq_sym _ _ _ (@comp_assoc (Functor_cat K C)
  (@one_cat_native_snake_fourth_quotient_cover_source K C C1 Prod t Add T0 P Q N A B X D b c h)
  (@kernel_adjunction_family_func K C (@additive_preadditive C Prod t Add) t (@additive_terminal_object C Prod t
  Add) P (@transf_arrow_diagram_func K C X D c)) X (@cokernel_adjunction_family_func K C (@additive_preadditive
  C Prod t Add) t T0 Q (@transf_arrow_diagram_func K C B X b)) (@cokernel_adjunction_family_projection_transf K
  C (@additive_preadditive C Prod t Add) t T0 Q (@transf_arrow_diagram_func K C B X b))
  (@kernel_adjunction_family_inclusion_transf K C (@additive_preadditive C Prod t Add) t
  (@additive_terminal_object C Prod t Add) P (@transf_arrow_diagram_func K C X D c))
  (@one_cat_native_snake_fourth_kernel_lift K C C1 Prod t Add T0 P Q N A B X D b c h))) (@eq_trans _ _ _ _
  (@eq_ap (@Transf K C (@one_cat_native_snake_fourth_quotient_cover_source K C C1 Prod t Add T0 P Q N A B X D b
  c h) X) (@Transf K C (@one_cat_native_snake_fourth_quotient_cover_source K C C1 Prod t Add T0 P Q N A B X D b
  c h) (@cokernel_adjunction_family_func K C (@additive_preadditive C Prod t Add) t T0 Q
  (@transf_arrow_diagram_func K C B X b))) (λ v : τ (@Transf K C
  (@one_cat_native_snake_fourth_quotient_cover_source K C C1 Prod t Add T0 P Q N A B X D b c h) X), (@comp_fapp0
  (Functor_cat K C) (@one_cat_native_snake_fourth_quotient_cover_source K C C1 Prod t Add T0 P Q N A B X D b c
  h) X (@cokernel_adjunction_family_func K C (@additive_preadditive C Prod t Add) t T0 Q
  (@transf_arrow_diagram_func K C B X b)) (@cokernel_adjunction_family_projection_transf K C
  (@additive_preadditive C Prod t Add) t T0 Q (@transf_arrow_diagram_func K C B X b)) v)) _ _
  (@one_cat_native_snake_fourth_kernel_reconstruction K C C1 Prod t Add T0 P Q N A B X D b c h)) (@eq_trans _ _
  _ _ (@one_cat_native_snake_fourth_difference_quotient_path K C C1 Prod t Add T0 P Q N A B X D b c h)
  (@eq_trans _ _ _ _ (@comp_assoc (Functor_cat K C) (@one_cat_native_snake_fourth_quotient_cover_source K C C1
  Prod t Add T0 P Q N A B X D b c h) (@one_cat_native_snake_fourth_gamma_cover_source K C C1 Prod t Add T0 P Q N
  A B X D b c h) X (@cokernel_adjunction_family_func K C (@additive_preadditive C Prod t Add) t T0 Q
  (@transf_arrow_diagram_func K C B X b)) (@cokernel_adjunction_family_projection_transf K C
  (@additive_preadditive C Prod t Add) t T0 Q (@transf_arrow_diagram_func K C B X b)) (@comp_fapp0 (Functor_cat
  K C) (@one_cat_native_snake_fourth_gamma_cover_source K C C1 Prod t Add T0 P Q N A B X D b c h)
  (@one_cat_native_snake_fourth_cover_source K C C1 Prod t Add T0 P Q N A B X D b c h) X
  (@one_cat_native_snake_fourth_cover_lift K C C1 Prod t Add T0 P Q N A B X D b c h)
  (@one_cat_native_snake_fourth_gamma_cover_first K C C1 Prod t Add T0 P Q N A B X D b c h))
  (@one_cat_native_snake_fourth_quotient_cover_first K C C1 Prod t Add T0 P Q N A B X D b c h)) (@eq_trans _ _ _
  _ (@eq_ap (@Transf K C (@one_cat_native_snake_fourth_gamma_cover_source K C C1 Prod t Add T0 P Q N A B X D b c
  h) (@cokernel_adjunction_family_func K C (@additive_preadditive C Prod t Add) t T0 Q
  (@transf_arrow_diagram_func K C B X b))) (@Transf K C (@one_cat_native_snake_fourth_quotient_cover_source K C
  C1 Prod t Add T0 P Q N A B X D b c h) (@cokernel_adjunction_family_func K C (@additive_preadditive C Prod t
  Add) t T0 Q (@transf_arrow_diagram_func K C B X b))) (λ v : τ (@Transf K C
  (@one_cat_native_snake_fourth_gamma_cover_source K C C1 Prod t Add T0 P Q N A B X D b c h)
  (@cokernel_adjunction_family_func K C (@additive_preadditive C Prod t Add) t T0 Q (@transf_arrow_diagram_func
  K C B X b))), (@comp_fapp0 (Functor_cat K C) (@one_cat_native_snake_fourth_quotient_cover_source K C C1 Prod t
  Add T0 P Q N A B X D b c h) (@one_cat_native_snake_fourth_gamma_cover_source K C C1 Prod t Add T0 P Q N A B X
  D b c h) (@cokernel_adjunction_family_func K C (@additive_preadditive C Prod t Add) t T0 Q
  (@transf_arrow_diagram_func K C B X b)) v (@one_cat_native_snake_fourth_quotient_cover_first K C C1 Prod t Add
  T0 P Q N A B X D b c h))) _ _ (@eq_trans _ _ _ _ (@comp_assoc (Functor_cat K C)
  (@one_cat_native_snake_fourth_gamma_cover_source K C C1 Prod t Add T0 P Q N A B X D b c h)
  (@one_cat_native_snake_fourth_cover_source K C C1 Prod t Add T0 P Q N A B X D b c h) X
  (@cokernel_adjunction_family_func K C (@additive_preadditive C Prod t Add) t T0 Q (@transf_arrow_diagram_func
  K C B X b)) (@cokernel_adjunction_family_projection_transf K C (@additive_preadditive C Prod t Add) t T0 Q
  (@transf_arrow_diagram_func K C B X b)) (@one_cat_native_snake_fourth_cover_lift K C C1 Prod t Add T0 P Q N A
  B X D b c h) (@one_cat_native_snake_fourth_gamma_cover_first K C C1 Prod t Add T0 P Q N A B X D b c h))
  (@eq_trans _ _ _ _ (@eq_ap (@Transf K C (@one_cat_native_snake_fourth_cover_source K C C1 Prod t Add T0 P Q N
  A B X D b c h) (@cokernel_adjunction_family_func K C (@additive_preadditive C Prod t Add) t T0 Q
  (@transf_arrow_diagram_func K C B X b))) (@Transf K C (@one_cat_native_snake_fourth_gamma_cover_source K C C1
  Prod t Add T0 P Q N A B X D b c h) (@cokernel_adjunction_family_func K C (@additive_preadditive C Prod t Add)
  t T0 Q (@transf_arrow_diagram_func K C B X b))) (λ v : τ (@Transf K C
  (@one_cat_native_snake_fourth_cover_source K C C1 Prod t Add T0 P Q N A B X D b c h)
  (@cokernel_adjunction_family_func K C (@additive_preadditive C Prod t Add) t T0 Q (@transf_arrow_diagram_func
  K C B X b))), (@comp_fapp0 (Functor_cat K C) (@one_cat_native_snake_fourth_gamma_cover_source K C C1 Prod t
  Add T0 P Q N A B X D b c h) (@one_cat_native_snake_fourth_cover_source K C C1 Prod t Add T0 P Q N A B X D b c
  h) (@cokernel_adjunction_family_func K C (@additive_preadditive C Prod t Add) t T0 Q
  (@transf_arrow_diagram_func K C B X b)) v (@one_cat_native_snake_fourth_gamma_cover_first K C C1 Prod t Add T0
  P Q N A B X D b c h))) _ _ (@eq_sym _ _ _ (@one_cat_native_snake_fourth_cover_compatibility K C C1 Prod t Add
  T0 P Q N A B X D b c h))) (@eq_sym _ _ _ (@comp_assoc (Functor_cat K C)
  (@one_cat_native_snake_fourth_gamma_cover_source K C C1 Prod t Add T0 P Q N A B X D b c h)
  (@one_cat_native_snake_fourth_cover_source K C C1 Prod t Add T0 P Q N A B X D b c h)
  (@kernel_adjunction_family_func K C (@additive_preadditive C Prod t Add) t (@additive_terminal_object C Prod t
  Add) P (@transf_arrow_diagram_func K C (@cokernel_adjunction_family_func K C (@additive_preadditive C Prod t
  Add) t T0 Q (@transf_arrow_diagram_func K C B X b)) (@cokernel_adjunction_family_func K C
  (@additive_preadditive C Prod t Add) t T0 Q (@one_cat_native_snake_gamma_diagram K C (@additive_preadditive C
  Prod t Add) C1 t (@additive_terminal_object C Prod t Add) T0 Q A B X D b c h))
  (@one_cat_native_snake_cokernel_second K C (@additive_preadditive C Prod t Add) C1 t
  (@additive_terminal_object C Prod t Add) T0 P Q A B X D b c h))) (@cokernel_adjunction_family_func K C
  (@additive_preadditive C Prod t Add) t T0 Q (@transf_arrow_diagram_func K C B X b))
  (@kernel_adjunction_family_inclusion_transf K C (@additive_preadditive C Prod t Add) t
  (@additive_terminal_object C Prod t Add) P (@transf_arrow_diagram_func K C (@cokernel_adjunction_family_func K
  C (@additive_preadditive C Prod t Add) t T0 Q (@transf_arrow_diagram_func K C B X b))
  (@cokernel_adjunction_family_func K C (@additive_preadditive C Prod t Add) t T0 Q
  (@one_cat_native_snake_gamma_diagram K C (@additive_preadditive C Prod t Add) C1 t (@additive_terminal_object
  C Prod t Add) T0 Q A B X D b c h)) (@one_cat_native_snake_cokernel_second K C (@additive_preadditive C Prod t
  Add) C1 t (@additive_terminal_object C Prod t Add) T0 P Q A B X D b c h)))
  (@one_cat_native_snake_fourth_cover_projection K C C1 Prod t Add T0 P Q N A B X D b c h)
  (@one_cat_native_snake_fourth_gamma_cover_first K C C1 Prod t Add T0 P Q N A B X D b c h)))))) (@eq_sym _ _ _
  (@comp_assoc (Functor_cat K C) (@one_cat_native_snake_fourth_quotient_cover_source K C C1 Prod t Add T0 P Q N
  A B X D b c h) (@one_cat_native_snake_fourth_gamma_cover_source K C C1 Prod t Add T0 P Q N A B X D b c h)
  (@kernel_adjunction_family_func K C (@additive_preadditive C Prod t Add) t (@additive_terminal_object C Prod t
  Add) P (@transf_arrow_diagram_func K C (@cokernel_adjunction_family_func K C (@additive_preadditive C Prod t
  Add) t T0 Q (@transf_arrow_diagram_func K C B X b)) (@cokernel_adjunction_family_func K C
  (@additive_preadditive C Prod t Add) t T0 Q (@one_cat_native_snake_gamma_diagram K C (@additive_preadditive C
  Prod t Add) C1 t (@additive_terminal_object C Prod t Add) T0 Q A B X D b c h))
  (@one_cat_native_snake_cokernel_second K C (@additive_preadditive C Prod t Add) C1 t
  (@additive_terminal_object C Prod t Add) T0 P Q A B X D b c h))) (@cokernel_adjunction_family_func K C
  (@additive_preadditive C Prod t Add) t T0 Q (@transf_arrow_diagram_func K C B X b))
  (@kernel_adjunction_family_inclusion_transf K C (@additive_preadditive C Prod t Add) t
  (@additive_terminal_object C Prod t Add) P (@transf_arrow_diagram_func K C (@cokernel_adjunction_family_func K
  C (@additive_preadditive C Prod t Add) t T0 Q (@transf_arrow_diagram_func K C B X b))
  (@cokernel_adjunction_family_func K C (@additive_preadditive C Prod t Add) t T0 Q
  (@one_cat_native_snake_gamma_diagram K C (@additive_preadditive C Prod t Add) C1 t (@additive_terminal_object
  C Prod t Add) T0 Q A B X D b c h)) (@one_cat_native_snake_cokernel_second K C (@additive_preadditive C Prod t
  Add) C1 t (@additive_terminal_object C Prod t Add) T0 P Q A B X D b c h))) (@comp_fapp0 (Functor_cat K C)
  (@one_cat_native_snake_fourth_gamma_cover_source K C C1 Prod t Add T0 P Q N A B X D b c h)
  (@one_cat_native_snake_fourth_cover_source K C C1 Prod t Add T0 P Q N A B X D b c h)
  (@kernel_adjunction_family_func K C (@additive_preadditive C Prod t Add) t (@additive_terminal_object C Prod t
  Add) P (@transf_arrow_diagram_func K C (@cokernel_adjunction_family_func K C (@additive_preadditive C Prod t
  Add) t T0 Q (@transf_arrow_diagram_func K C B X b)) (@cokernel_adjunction_family_func K C
  (@additive_preadditive C Prod t Add) t T0 Q (@one_cat_native_snake_gamma_diagram K C (@additive_preadditive C
  Prod t Add) C1 t (@additive_terminal_object C Prod t Add) T0 Q A B X D b c h))
  (@one_cat_native_snake_cokernel_second K C (@additive_preadditive C Prod t Add) C1 t
  (@additive_terminal_object C Prod t Add) T0 P Q A B X D b c h)))
  (@one_cat_native_snake_fourth_cover_projection K C C1 Prod t Add T0 P Q N A B X D b c h)
  (@one_cat_native_snake_fourth_gamma_cover_first K C C1 Prod t Add T0 P Q N A B X D b c h))
  (@one_cat_native_snake_fourth_quotient_cover_first K C C1 Prod t Add T0 P Q N A B X D b c h))))))))));
