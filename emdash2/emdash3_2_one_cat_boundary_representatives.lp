/* Whole boundary representatives through the original image/coimage and K/Q. */
require open emdash.emdash3_2_one_cat_homology_representatives;

// Present the original quotient-zero law at its original image diagram.
symbol one_cat_boundary_image_input_zero [B C : Cat] (C1 : τ (IsNCat (cat_succ cat_zero) C)) [Prod : τ
  (Functor (Product_cat C C) C)] [t : τ (Obj C)] (A : τ (@AdditiveCategory C Prod t)) (T0 : τ (@TerminalObject
  (Op_cat C) t)) (P : τ (@KernelAdjunctionStructure C (@additive_preadditive C Prod t A) t
  (@additive_terminal_object C Prod t A))) (Q : τ (@CokernelAdjunctionStructure C (@additive_preadditive C Prod t
  A) t T0)) (N : τ (@OneCatAdjunctionNormality C (@additive_preadditive C Prod t A) C1 t
  (@additive_terminal_object C Prod t A) T0 P Q)) (U : τ (Functor B C)) (D : τ (Functor B (Functor_cat
  WalkingArrow_cat C))) (h : τ (@Transf B (Functor_cat WalkingArrow_cat C) (@comp_cat_fapp0 B C (Functor_cat
  WalkingArrow_cat C) (@terminal_arrow_diagram_func C t (@additive_terminal_object C Prod t A)) U) D)) (X : τ
  (Functor B C)) (v : τ (@Transf B C X (@kernel_adjunction_family_func B C (@additive_preadditive C Prod t A) t
  (@additive_terminal_object C Prod t A) P D))) (z : τ (@= (@Transf B C X (@homology_adjunction_family_func B C
  (@additive_preadditive C Prod t A) t (@additive_terminal_object C Prod t A) T0 P Q U D h)) (@comp_fapp0
  (Functor_cat B C) X (@kernel_adjunction_family_func B C (@additive_preadditive C Prod t A) t
  (@additive_terminal_object C Prod t A) P D) (@homology_adjunction_family_func B C (@additive_preadditive C Prod
  t A) t (@additive_terminal_object C Prod t A) T0 P Q U D h) (@homology_adjunction_family_projection_transf B C
  (@additive_preadditive C Prod t A) t (@additive_terminal_object C Prod t A) T0 P Q U D h) v)
  (@zero_arrow_family_zero_transf B C t (@additive_terminal_object C Prod t A) T0 X
  (@homology_adjunction_family_func B C (@additive_preadditive C Prod t A) t (@additive_terminal_object C Prod t
  A) T0 P Q U D h))))
 : τ (@= (@Transf B C X (@diagram_family_at_func B WalkingArrow_cat C (@comp_cat_fapp0 B (Functor_cat
  WalkingArrow_cat C) (Functor_cat WalkingArrow_cat C) (@cokernel_adjunction_arrow_func C (@additive_preadditive C
  Prod t A) t T0 Q) (@kernel_adjunction_family_boundary_diagram_func B C (@additive_preadditive C Prod t A) t
  (@additive_terminal_object C Prod t A) P U D h)) walking_arrow_tgt)) (@comp_fapp0 (Functor_cat B C) X
  (@kernel_adjunction_family_func B C (@additive_preadditive C Prod t A) t (@additive_terminal_object C Prod t A)
  P D) (@diagram_family_at_func B WalkingArrow_cat C (@comp_cat_fapp0 B (Functor_cat WalkingArrow_cat C)
  (Functor_cat WalkingArrow_cat C) (@cokernel_adjunction_arrow_func C (@additive_preadditive C Prod t A) t T0 Q)
  (@kernel_adjunction_family_boundary_diagram_func B C (@additive_preadditive C Prod t A) t
  (@additive_terminal_object C Prod t A) P U D h)) walking_arrow_tgt) (@diagram_family_transf B WalkingArrow_cat C
  (@comp_cat_fapp0 B (Functor_cat WalkingArrow_cat C) (Functor_cat WalkingArrow_cat C)
  (@cokernel_adjunction_arrow_func C (@additive_preadditive C Prod t A) t T0 Q)
  (@kernel_adjunction_family_boundary_diagram_func B C (@additive_preadditive C Prod t A) t
  (@additive_terminal_object C Prod t A) P U D h)) walking_arrow_src walking_arrow_tgt walking_arrow_generator) v)
  (@zero_arrow_family_zero_transf B C t (@additive_terminal_object C Prod t A) T0 X (@diagram_family_at_func B
  WalkingArrow_cat C (@comp_cat_fapp0 B (Functor_cat WalkingArrow_cat C) (Functor_cat WalkingArrow_cat C)
  (@cokernel_adjunction_arrow_func C (@additive_preadditive C Prod t A) t T0 Q)
  (@kernel_adjunction_family_boundary_diagram_func B C (@additive_preadditive C Prod t A) t
  (@additive_terminal_object C Prod t A) P U D h)) walking_arrow_tgt)))
≔ (@eq_trans _ _ _ _ z (@eq_ap (@Transf B C (@Const_func B C t) (@diagram_family_at_func B WalkingArrow_cat C
  (@comp_cat_fapp0 B (Functor_cat WalkingArrow_cat C) (Functor_cat WalkingArrow_cat C)
  (@cokernel_adjunction_arrow_func C (@additive_preadditive C Prod t A) t T0 Q)
  (@kernel_adjunction_family_boundary_diagram_func B C (@additive_preadditive C Prod t A) t
  (@additive_terminal_object C Prod t A) P U D h)) walking_arrow_tgt)) (@Transf B C X (@diagram_family_at_func B
  WalkingArrow_cat C (@comp_cat_fapp0 B (Functor_cat WalkingArrow_cat C) (Functor_cat WalkingArrow_cat C)
  (@cokernel_adjunction_arrow_func C (@additive_preadditive C Prod t A) t T0 Q)
  (@kernel_adjunction_family_boundary_diagram_func B C (@additive_preadditive C Prod t A) t
  (@additive_terminal_object C Prod t A) P U D h)) walking_arrow_tgt)) (λ j : τ (@Transf B C (@Const_func B C t)
  (@diagram_family_at_func B WalkingArrow_cat C (@comp_cat_fapp0 B (Functor_cat WalkingArrow_cat C) (Functor_cat
  WalkingArrow_cat C) (@cokernel_adjunction_arrow_func C (@additive_preadditive C Prod t A) t T0 Q)
  (@kernel_adjunction_family_boundary_diagram_func B C (@additive_preadditive C Prod t A) t
  (@additive_terminal_object C Prod t A) P U D h)) walking_arrow_tgt)), (@comp_fapp0 (Functor_cat B C) X
  (@Const_func B C t) (@diagram_family_at_func B WalkingArrow_cat C (@comp_cat_fapp0 B (Functor_cat
  WalkingArrow_cat C) (Functor_cat WalkingArrow_cat C) (@cokernel_adjunction_arrow_func C (@additive_preadditive C
  Prod t A) t T0 Q) (@kernel_adjunction_family_boundary_diagram_func B C (@additive_preadditive C Prod t A) t
  (@additive_terminal_object C Prod t A) P U D h)) walking_arrow_tgt) j (@diagram_family_transf B WalkingArrow_cat
  C (@comp_cat_fapp0 B C (Functor_cat WalkingArrow_cat C) (@terminal_arrow_diagram_func C t
  (@additive_terminal_object C Prod t A)) X) walking_arrow_src walking_arrow_tgt walking_arrow_generator)))
  (@diagram_family_transf B WalkingArrow_cat C (@comp_cat_fapp0 B C (Functor_cat WalkingArrow_cat C)
  (@initial_arrow_diagram_func C t T0) (@homology_adjunction_family_func B C (@additive_preadditive C Prod t A) t
  (@additive_terminal_object C Prod t A) T0 P Q U D h)) walking_arrow_src walking_arrow_tgt
  walking_arrow_generator) (@diagram_family_transf B WalkingArrow_cat C (@comp_cat_fapp0 B C (Functor_cat
  WalkingArrow_cat C) (@initial_arrow_diagram_func C t T0) (@diagram_family_at_func B WalkingArrow_cat C
  (@comp_cat_fapp0 B (Functor_cat WalkingArrow_cat C) (Functor_cat WalkingArrow_cat C)
  (@cokernel_adjunction_arrow_func C (@additive_preadditive C Prod t A) t T0 Q)
  (@kernel_adjunction_family_boundary_diagram_func B C (@additive_preadditive C Prod t A) t
  (@additive_terminal_object C Prod t A) P U D h)) walking_arrow_tgt)) walking_arrow_src walking_arrow_tgt
  walking_arrow_generator) (@one_cat_initial_family_arrow_path B C C1 t T0 (@diagram_family_at_func B
  WalkingArrow_cat C (@comp_cat_fapp0 B (Functor_cat WalkingArrow_cat C) (Functor_cat WalkingArrow_cat C)
  (@cokernel_adjunction_arrow_func C (@additive_preadditive C Prod t A) t T0 Q)
  (@kernel_adjunction_family_boundary_diagram_func B C (@additive_preadditive C Prod t A) t
  (@additive_terminal_object C Prod t A) P U D h)) walking_arrow_tgt) (@diagram_family_transf B WalkingArrow_cat C
  (@comp_cat_fapp0 B C (Functor_cat WalkingArrow_cat C) (@initial_arrow_diagram_func C t T0)
  (@homology_adjunction_family_func B C (@additive_preadditive C Prod t A) t (@additive_terminal_object C Prod t
  A) T0 P Q U D h)) walking_arrow_src walking_arrow_tgt walking_arrow_generator))));

// The original K mate lifts a whole quotient-zero cycle to the original image.
symbol one_cat_boundary_image_lift [B C : Cat] (C1 : τ (IsNCat (cat_succ cat_zero) C)) [Prod : τ (Functor
  (Product_cat C C) C)] [t : τ (Obj C)] (A : τ (@AdditiveCategory C Prod t)) (T0 : τ (@TerminalObject (Op_cat C)
  t)) (P : τ (@KernelAdjunctionStructure C (@additive_preadditive C Prod t A) t (@additive_terminal_object C Prod
  t A))) (Q : τ (@CokernelAdjunctionStructure C (@additive_preadditive C Prod t A) t T0)) (N : τ
  (@OneCatAdjunctionNormality C (@additive_preadditive C Prod t A) C1 t (@additive_terminal_object C Prod t A) T0
  P Q)) (U : τ (Functor B C)) (D : τ (Functor B (Functor_cat WalkingArrow_cat C))) (h : τ (@Transf B (Functor_cat
  WalkingArrow_cat C) (@comp_cat_fapp0 B C (Functor_cat WalkingArrow_cat C) (@terminal_arrow_diagram_func C t
  (@additive_terminal_object C Prod t A)) U) D)) (X : τ (Functor B C)) (v : τ (@Transf B C X
  (@kernel_adjunction_family_func B C (@additive_preadditive C Prod t A) t (@additive_terminal_object C Prod t A)
  P D))) (z : τ (@= (@Transf B C X (@homology_adjunction_family_func B C (@additive_preadditive C Prod t A) t
  (@additive_terminal_object C Prod t A) T0 P Q U D h)) (@comp_fapp0 (Functor_cat B C) X
  (@kernel_adjunction_family_func B C (@additive_preadditive C Prod t A) t (@additive_terminal_object C Prod t A)
  P D) (@homology_adjunction_family_func B C (@additive_preadditive C Prod t A) t (@additive_terminal_object C
  Prod t A) T0 P Q U D h) (@homology_adjunction_family_projection_transf B C (@additive_preadditive C Prod t A) t
  (@additive_terminal_object C Prod t A) T0 P Q U D h) v) (@zero_arrow_family_zero_transf B C t
  (@additive_terminal_object C Prod t A) T0 X (@homology_adjunction_family_func B C (@additive_preadditive C Prod
  t A) t (@additive_terminal_object C Prod t A) T0 P Q U D h))))
 : τ (@Transf B C X (@comp_cat_fapp0 B (Functor_cat WalkingArrow_cat C) C (@adjunction_image_func C
  (@additive_preadditive C Prod t A) t (@additive_terminal_object C Prod t A) T0 P Q)
  (@kernel_adjunction_family_boundary_diagram_func B C (@additive_preadditive C Prod t A) t
  (@additive_terminal_object C Prod t A) P U D h)))
≔ @one_cat_kernel_family_lift B C (@additive_preadditive C Prod t A) C1 t (@additive_terminal_object C Prod t A)
  T0 P X (@comp_cat_fapp0 B (Functor_cat WalkingArrow_cat C) (Functor_cat WalkingArrow_cat C)
  (@cokernel_adjunction_arrow_func C (@additive_preadditive C Prod t A) t T0 Q)
  (@kernel_adjunction_family_boundary_diagram_func B C (@additive_preadditive C Prod t A) t
  (@additive_terminal_object C Prod t A) P U D h)) v (@one_cat_boundary_image_input_zero B C C1 Prod t A T0
  P Q N U D h X v z);

// The original image inclusion reconstructs that whole cycle.
symbol one_cat_boundary_image_lift_reconstruction [B C : Cat] (C1 : τ (IsNCat (cat_succ cat_zero) C)) [Prod
  : τ (Functor (Product_cat C C) C)] [t : τ (Obj C)] (A : τ (@AdditiveCategory C Prod t)) (T0 : τ (@TerminalObject
  (Op_cat C) t)) (P : τ (@KernelAdjunctionStructure C (@additive_preadditive C Prod t A) t
  (@additive_terminal_object C Prod t A))) (Q : τ (@CokernelAdjunctionStructure C (@additive_preadditive C Prod t
  A) t T0)) (N : τ (@OneCatAdjunctionNormality C (@additive_preadditive C Prod t A) C1 t
  (@additive_terminal_object C Prod t A) T0 P Q)) (U : τ (Functor B C)) (D : τ (Functor B (Functor_cat
  WalkingArrow_cat C))) (h : τ (@Transf B (Functor_cat WalkingArrow_cat C) (@comp_cat_fapp0 B C (Functor_cat
  WalkingArrow_cat C) (@terminal_arrow_diagram_func C t (@additive_terminal_object C Prod t A)) U) D)) (X : τ
  (Functor B C)) (v : τ (@Transf B C X (@kernel_adjunction_family_func B C (@additive_preadditive C Prod t A) t
  (@additive_terminal_object C Prod t A) P D))) (z : τ (@= (@Transf B C X (@homology_adjunction_family_func B C
  (@additive_preadditive C Prod t A) t (@additive_terminal_object C Prod t A) T0 P Q U D h)) (@comp_fapp0
  (Functor_cat B C) X (@kernel_adjunction_family_func B C (@additive_preadditive C Prod t A) t
  (@additive_terminal_object C Prod t A) P D) (@homology_adjunction_family_func B C (@additive_preadditive C Prod
  t A) t (@additive_terminal_object C Prod t A) T0 P Q U D h) (@homology_adjunction_family_projection_transf B C
  (@additive_preadditive C Prod t A) t (@additive_terminal_object C Prod t A) T0 P Q U D h) v)
  (@zero_arrow_family_zero_transf B C t (@additive_terminal_object C Prod t A) T0 X
  (@homology_adjunction_family_func B C (@additive_preadditive C Prod t A) t (@additive_terminal_object C Prod t
  A) T0 P Q U D h))))
 : τ (@= (@Transf B C X (@kernel_adjunction_family_func B C (@additive_preadditive C Prod t A) t
  (@additive_terminal_object C Prod t A) P D)) (@comp_fapp0 (Functor_cat B C) X (@comp_cat_fapp0 B (Functor_cat
  WalkingArrow_cat C) C (@adjunction_image_func C (@additive_preadditive C Prod t A) t (@additive_terminal_object
  C Prod t A) T0 P Q) (@kernel_adjunction_family_boundary_diagram_func B C (@additive_preadditive C Prod t A) t
  (@additive_terminal_object C Prod t A) P U D h)) (@kernel_adjunction_family_func B C (@additive_preadditive C
  Prod t A) t (@additive_terminal_object C Prod t A) P D) (@kernel_adjunction_family_inclusion_transf B C
  (@additive_preadditive C Prod t A) t (@additive_terminal_object C Prod t A) P (@comp_cat_fapp0 B (Functor_cat
  WalkingArrow_cat C) (Functor_cat WalkingArrow_cat C) (@cokernel_adjunction_arrow_func C (@additive_preadditive C
  Prod t A) t T0 Q) (@kernel_adjunction_family_boundary_diagram_func B C (@additive_preadditive C Prod t A) t
  (@additive_terminal_object C Prod t A) P U D h))) (@one_cat_boundary_image_lift B C C1 Prod t A T0 P Q N U
  D h X v z)) v)
≔ @one_cat_kernel_family_lift_ambient_reconstruction B C (@additive_preadditive C Prod t A) C1 t
  (@additive_terminal_object C Prod t A) T0 P X (@comp_cat_fapp0 B (Functor_cat WalkingArrow_cat C) (Functor_cat
  WalkingArrow_cat C) (@cokernel_adjunction_arrow_func C (@additive_preadditive C Prod t A) t T0 Q)
  (@kernel_adjunction_family_boundary_diagram_func B C (@additive_preadditive C Prod t A) t
  (@additive_terminal_object C Prod t A) P U D h)) v (@one_cat_boundary_image_input_zero B C C1 Prod t A T0
  P Q N U D h X v z);

// Original normality transports the lifted cycle to the original coimage.
symbol one_cat_boundary_coimage_lift [B C : Cat] (C1 : τ (IsNCat (cat_succ cat_zero) C)) [Prod : τ (Functor
  (Product_cat C C) C)] [t : τ (Obj C)] (A : τ (@AdditiveCategory C Prod t)) (T0 : τ (@TerminalObject (Op_cat C)
  t)) (P : τ (@KernelAdjunctionStructure C (@additive_preadditive C Prod t A) t (@additive_terminal_object C Prod
  t A))) (Q : τ (@CokernelAdjunctionStructure C (@additive_preadditive C Prod t A) t T0)) (N : τ
  (@OneCatAdjunctionNormality C (@additive_preadditive C Prod t A) C1 t (@additive_terminal_object C Prod t A) T0
  P Q)) (U : τ (Functor B C)) (D : τ (Functor B (Functor_cat WalkingArrow_cat C))) (h : τ (@Transf B (Functor_cat
  WalkingArrow_cat C) (@comp_cat_fapp0 B C (Functor_cat WalkingArrow_cat C) (@terminal_arrow_diagram_func C t
  (@additive_terminal_object C Prod t A)) U) D)) (X : τ (Functor B C)) (v : τ (@Transf B C X
  (@kernel_adjunction_family_func B C (@additive_preadditive C Prod t A) t (@additive_terminal_object C Prod t A)
  P D))) (z : τ (@= (@Transf B C X (@homology_adjunction_family_func B C (@additive_preadditive C Prod t A) t
  (@additive_terminal_object C Prod t A) T0 P Q U D h)) (@comp_fapp0 (Functor_cat B C) X
  (@kernel_adjunction_family_func B C (@additive_preadditive C Prod t A) t (@additive_terminal_object C Prod t A)
  P D) (@homology_adjunction_family_func B C (@additive_preadditive C Prod t A) t (@additive_terminal_object C
  Prod t A) T0 P Q U D h) (@homology_adjunction_family_projection_transf B C (@additive_preadditive C Prod t A) t
  (@additive_terminal_object C Prod t A) T0 P Q U D h) v) (@zero_arrow_family_zero_transf B C t
  (@additive_terminal_object C Prod t A) T0 X (@homology_adjunction_family_func B C (@additive_preadditive C Prod
  t A) t (@additive_terminal_object C Prod t A) T0 P Q U D h))))
 : τ (@Transf B C X (@comp_cat_fapp0 B (Functor_cat WalkingArrow_cat C) C (@adjunction_coimage_func C
  (@additive_preadditive C Prod t A) t (@additive_terminal_object C Prod t A) T0 P Q)
  (@kernel_adjunction_family_boundary_diagram_func B C (@additive_preadditive C Prod t A) t
  (@additive_terminal_object C Prod t A) P U D h)))
≔ (@comp_fapp0 (Functor_cat B C) X (@comp_cat_fapp0 B (Functor_cat WalkingArrow_cat C) C (@adjunction_image_func C
  (@additive_preadditive C Prod t A) t (@additive_terminal_object C Prod t A) T0 P Q)
  (@kernel_adjunction_family_boundary_diagram_func B C (@additive_preadditive C Prod t A) t
  (@additive_terminal_object C Prod t A) P U D h)) (@comp_cat_fapp0 B (Functor_cat WalkingArrow_cat C) C
  (@adjunction_coimage_func C (@additive_preadditive C Prod t A) t (@additive_terminal_object C Prod t A) T0 P Q)
  (@kernel_adjunction_family_boundary_diagram_func B C (@additive_preadditive C Prod t A) t
  (@additive_terminal_object C Prod t A) P U D h)) (@fapp0 _ _ (@comp_cat_con_fapp1_func B (Functor_cat
  WalkingArrow_cat C) C (@kernel_adjunction_family_boundary_diagram_func B C (@additive_preadditive C Prod t A) t
  (@additive_terminal_object C Prod t A) P U D h) (@adjunction_image_func C (@additive_preadditive C Prod t A) t
  (@additive_terminal_object C Prod t A) T0 P Q) (@adjunction_coimage_func C (@additive_preadditive C Prod t A) t
  (@additive_terminal_object C Prod t A) T0 P Q)) (@one_cat_coimage_image_inverse_transf C (@additive_preadditive
  C Prod t A) C1 t (@additive_terminal_object C Prod t A) T0 P Q N)) (@one_cat_boundary_image_lift B C C1
  Prod t A T0 P Q N U D h X v z));

// The original coimage factor reconstructs the original quotient-zero cycle.
symbol one_cat_boundary_coimage_lift_reconstruction [B C : Cat] (C1 : τ (IsNCat (cat_succ cat_zero) C))
  [Prod : τ (Functor (Product_cat C C) C)] [t : τ (Obj C)] (A : τ (@AdditiveCategory C Prod t)) (T0 : τ
  (@TerminalObject (Op_cat C) t)) (P : τ (@KernelAdjunctionStructure C (@additive_preadditive C Prod t A) t
  (@additive_terminal_object C Prod t A))) (Q : τ (@CokernelAdjunctionStructure C (@additive_preadditive C Prod t
  A) t T0)) (N : τ (@OneCatAdjunctionNormality C (@additive_preadditive C Prod t A) C1 t
  (@additive_terminal_object C Prod t A) T0 P Q)) (U : τ (Functor B C)) (D : τ (Functor B (Functor_cat
  WalkingArrow_cat C))) (h : τ (@Transf B (Functor_cat WalkingArrow_cat C) (@comp_cat_fapp0 B C (Functor_cat
  WalkingArrow_cat C) (@terminal_arrow_diagram_func C t (@additive_terminal_object C Prod t A)) U) D)) (X : τ
  (Functor B C)) (v : τ (@Transf B C X (@kernel_adjunction_family_func B C (@additive_preadditive C Prod t A) t
  (@additive_terminal_object C Prod t A) P D))) (z : τ (@= (@Transf B C X (@homology_adjunction_family_func B C
  (@additive_preadditive C Prod t A) t (@additive_terminal_object C Prod t A) T0 P Q U D h)) (@comp_fapp0
  (Functor_cat B C) X (@kernel_adjunction_family_func B C (@additive_preadditive C Prod t A) t
  (@additive_terminal_object C Prod t A) P D) (@homology_adjunction_family_func B C (@additive_preadditive C Prod
  t A) t (@additive_terminal_object C Prod t A) T0 P Q U D h) (@homology_adjunction_family_projection_transf B C
  (@additive_preadditive C Prod t A) t (@additive_terminal_object C Prod t A) T0 P Q U D h) v)
  (@zero_arrow_family_zero_transf B C t (@additive_terminal_object C Prod t A) T0 X
  (@homology_adjunction_family_func B C (@additive_preadditive C Prod t A) t (@additive_terminal_object C Prod t
  A) T0 P Q U D h))))
 : τ (@= (@Transf B C X (@kernel_adjunction_family_func B C (@additive_preadditive C Prod t A) t
  (@additive_terminal_object C Prod t A) P D)) (@comp_fapp0 (Functor_cat B C) X (@comp_cat_fapp0 B (Functor_cat
  WalkingArrow_cat C) C (@adjunction_coimage_func C (@additive_preadditive C Prod t A) t
  (@additive_terminal_object C Prod t A) T0 P Q) (@kernel_adjunction_family_boundary_diagram_func B C
  (@additive_preadditive C Prod t A) t (@additive_terminal_object C Prod t A) P U D h))
  (@kernel_adjunction_family_func B C (@additive_preadditive C Prod t A) t (@additive_terminal_object C Prod t A)
  P D) (@fapp0 _ _ (@comp_cat_con_fapp1_func B (Functor_cat WalkingArrow_cat C) C
  (@kernel_adjunction_family_boundary_diagram_func B C (@additive_preadditive C Prod t A) t
  (@additive_terminal_object C Prod t A) P U D h) (@adjunction_coimage_func C (@additive_preadditive C Prod t A) t
  (@additive_terminal_object C Prod t A) T0 P Q) (@diagram_evaluation_at_func WalkingArrow_cat C
  walking_arrow_tgt)) (@one_cat_adjunction_coimage_to_target C (@additive_preadditive C Prod t A) C1 t
  (@additive_terminal_object C Prod t A) T0 P Q)) (@one_cat_boundary_coimage_lift B C C1 Prod t A T0 P Q N U
  D h X v z)) v)
≔ (@eq_trans _ _ _ _ (@comp_assoc (Functor_cat B C) X (@comp_cat_fapp0 B (Functor_cat WalkingArrow_cat C) C
  (@adjunction_image_func C (@additive_preadditive C Prod t A) t (@additive_terminal_object C Prod t A) T0 P Q)
  (@kernel_adjunction_family_boundary_diagram_func B C (@additive_preadditive C Prod t A) t
  (@additive_terminal_object C Prod t A) P U D h)) (@comp_cat_fapp0 B (Functor_cat WalkingArrow_cat C) C
  (@adjunction_coimage_func C (@additive_preadditive C Prod t A) t (@additive_terminal_object C Prod t A) T0 P Q)
  (@kernel_adjunction_family_boundary_diagram_func B C (@additive_preadditive C Prod t A) t
  (@additive_terminal_object C Prod t A) P U D h)) (@kernel_adjunction_family_func B C (@additive_preadditive C
  Prod t A) t (@additive_terminal_object C Prod t A) P D) (@fapp0 _ _ (@comp_cat_con_fapp1_func B (Functor_cat
  WalkingArrow_cat C) C (@kernel_adjunction_family_boundary_diagram_func B C (@additive_preadditive C Prod t A) t
  (@additive_terminal_object C Prod t A) P U D h) (@adjunction_coimage_func C (@additive_preadditive C Prod t A) t
  (@additive_terminal_object C Prod t A) T0 P Q) (@diagram_evaluation_at_func WalkingArrow_cat C
  walking_arrow_tgt)) (@one_cat_adjunction_coimage_to_target C (@additive_preadditive C Prod t A) C1 t
  (@additive_terminal_object C Prod t A) T0 P Q)) (@fapp0 _ _ (@comp_cat_con_fapp1_func B (Functor_cat
  WalkingArrow_cat C) C (@kernel_adjunction_family_boundary_diagram_func B C (@additive_preadditive C Prod t A) t
  (@additive_terminal_object C Prod t A) P U D h) (@adjunction_image_func C (@additive_preadditive C Prod t A) t
  (@additive_terminal_object C Prod t A) T0 P Q) (@adjunction_coimage_func C (@additive_preadditive C Prod t A) t
  (@additive_terminal_object C Prod t A) T0 P Q)) (@one_cat_coimage_image_inverse_transf C (@additive_preadditive
  C Prod t A) C1 t (@additive_terminal_object C Prod t A) T0 P Q N)) (@one_cat_boundary_image_lift B C C1
  Prod t A T0 P Q N U D h X v z)) (@eq_trans _ _ _ _ (@eq_ap (@Transf B C (@comp_cat_fapp0 B (Functor_cat
  WalkingArrow_cat C) C (@adjunction_image_func C (@additive_preadditive C Prod t A) t (@additive_terminal_object
  C Prod t A) T0 P Q) (@kernel_adjunction_family_boundary_diagram_func B C (@additive_preadditive C Prod t A) t
  (@additive_terminal_object C Prod t A) P U D h)) (@kernel_adjunction_family_func B C (@additive_preadditive C
  Prod t A) t (@additive_terminal_object C Prod t A) P D)) (@Transf B C X (@kernel_adjunction_family_func B C
  (@additive_preadditive C Prod t A) t (@additive_terminal_object C Prod t A) P D)) (λ j : τ (@Transf B C
  (@comp_cat_fapp0 B (Functor_cat WalkingArrow_cat C) C (@adjunction_image_func C (@additive_preadditive C Prod t
  A) t (@additive_terminal_object C Prod t A) T0 P Q) (@kernel_adjunction_family_boundary_diagram_func B C
  (@additive_preadditive C Prod t A) t (@additive_terminal_object C Prod t A) P U D h))
  (@kernel_adjunction_family_func B C (@additive_preadditive C Prod t A) t (@additive_terminal_object C Prod t A)
  P D)), (@comp_fapp0 (Functor_cat B C) X (@comp_cat_fapp0 B (Functor_cat WalkingArrow_cat C) C
  (@adjunction_image_func C (@additive_preadditive C Prod t A) t (@additive_terminal_object C Prod t A) T0 P Q)
  (@kernel_adjunction_family_boundary_diagram_func B C (@additive_preadditive C Prod t A) t
  (@additive_terminal_object C Prod t A) P U D h)) (@kernel_adjunction_family_func B C (@additive_preadditive C
  Prod t A) t (@additive_terminal_object C Prod t A) P D) j (@one_cat_boundary_image_lift B C C1 Prod t A T0
  P Q N U D h X v z))) (@comp_fapp0 (Functor_cat B C) (@comp_cat_fapp0 B (Functor_cat WalkingArrow_cat C) C
  (@adjunction_image_func C (@additive_preadditive C Prod t A) t (@additive_terminal_object C Prod t A) T0 P Q)
  (@kernel_adjunction_family_boundary_diagram_func B C (@additive_preadditive C Prod t A) t
  (@additive_terminal_object C Prod t A) P U D h)) (@comp_cat_fapp0 B (Functor_cat WalkingArrow_cat C) C
  (@adjunction_coimage_func C (@additive_preadditive C Prod t A) t (@additive_terminal_object C Prod t A) T0 P Q)
  (@kernel_adjunction_family_boundary_diagram_func B C (@additive_preadditive C Prod t A) t
  (@additive_terminal_object C Prod t A) P U D h)) (@kernel_adjunction_family_func B C (@additive_preadditive C
  Prod t A) t (@additive_terminal_object C Prod t A) P D) (@fapp0 _ _ (@comp_cat_con_fapp1_func B (Functor_cat
  WalkingArrow_cat C) C (@kernel_adjunction_family_boundary_diagram_func B C (@additive_preadditive C Prod t A) t
  (@additive_terminal_object C Prod t A) P U D h) (@adjunction_coimage_func C (@additive_preadditive C Prod t A) t
  (@additive_terminal_object C Prod t A) T0 P Q) (@diagram_evaluation_at_func WalkingArrow_cat C
  walking_arrow_tgt)) (@one_cat_adjunction_coimage_to_target C (@additive_preadditive C Prod t A) C1 t
  (@additive_terminal_object C Prod t A) T0 P Q)) (@fapp0 _ _ (@comp_cat_con_fapp1_func B (Functor_cat
  WalkingArrow_cat C) C (@kernel_adjunction_family_boundary_diagram_func B C (@additive_preadditive C Prod t A) t
  (@additive_terminal_object C Prod t A) P U D h) (@adjunction_image_func C (@additive_preadditive C Prod t A) t
  (@additive_terminal_object C Prod t A) T0 P Q) (@adjunction_coimage_func C (@additive_preadditive C Prod t A) t
  (@additive_terminal_object C Prod t A) T0 P Q)) (@one_cat_coimage_image_inverse_transf C (@additive_preadditive
  C Prod t A) C1 t (@additive_terminal_object C Prod t A) T0 P Q N))) (@kernel_adjunction_family_inclusion_transf
  B C (@additive_preadditive C Prod t A) t (@additive_terminal_object C Prod t A) P (@comp_cat_fapp0 B
  (Functor_cat WalkingArrow_cat C) (Functor_cat WalkingArrow_cat C) (@cokernel_adjunction_arrow_func C
  (@additive_preadditive C Prod t A) t T0 Q) (@kernel_adjunction_family_boundary_diagram_func B C
  (@additive_preadditive C Prod t A) t (@additive_terminal_object C Prod t A) P U D h))) (@eq_trans _ _ _ _
  (@eq_ap (@Transf B C (@comp_cat_fapp0 B (Functor_cat WalkingArrow_cat C) C (@adjunction_coimage_func C
  (@additive_preadditive C Prod t A) t (@additive_terminal_object C Prod t A) T0 P Q)
  (@kernel_adjunction_family_boundary_diagram_func B C (@additive_preadditive C Prod t A) t
  (@additive_terminal_object C Prod t A) P U D h)) (@kernel_adjunction_family_func B C (@additive_preadditive C
  Prod t A) t (@additive_terminal_object C Prod t A) P D)) (@Transf B C (@comp_cat_fapp0 B (Functor_cat
  WalkingArrow_cat C) C (@adjunction_image_func C (@additive_preadditive C Prod t A) t (@additive_terminal_object
  C Prod t A) T0 P Q) (@kernel_adjunction_family_boundary_diagram_func B C (@additive_preadditive C Prod t A) t
  (@additive_terminal_object C Prod t A) P U D h)) (@kernel_adjunction_family_func B C (@additive_preadditive C
  Prod t A) t (@additive_terminal_object C Prod t A) P D)) (λ j : τ (@Transf B C (@comp_cat_fapp0 B (Functor_cat
  WalkingArrow_cat C) C (@adjunction_coimage_func C (@additive_preadditive C Prod t A) t
  (@additive_terminal_object C Prod t A) T0 P Q) (@kernel_adjunction_family_boundary_diagram_func B C
  (@additive_preadditive C Prod t A) t (@additive_terminal_object C Prod t A) P U D h))
  (@kernel_adjunction_family_func B C (@additive_preadditive C Prod t A) t (@additive_terminal_object C Prod t A)
  P D)), (@comp_fapp0 (Functor_cat B C) (@comp_cat_fapp0 B (Functor_cat WalkingArrow_cat C) C
  (@adjunction_image_func C (@additive_preadditive C Prod t A) t (@additive_terminal_object C Prod t A) T0 P Q)
  (@kernel_adjunction_family_boundary_diagram_func B C (@additive_preadditive C Prod t A) t
  (@additive_terminal_object C Prod t A) P U D h)) (@comp_cat_fapp0 B (Functor_cat WalkingArrow_cat C) C
  (@adjunction_coimage_func C (@additive_preadditive C Prod t A) t (@additive_terminal_object C Prod t A) T0 P Q)
  (@kernel_adjunction_family_boundary_diagram_func B C (@additive_preadditive C Prod t A) t
  (@additive_terminal_object C Prod t A) P U D h)) (@kernel_adjunction_family_func B C (@additive_preadditive C
  Prod t A) t (@additive_terminal_object C Prod t A) P D) j (@fapp0 _ _ (@comp_cat_con_fapp1_func B (Functor_cat
  WalkingArrow_cat C) C (@kernel_adjunction_family_boundary_diagram_func B C (@additive_preadditive C Prod t A) t
  (@additive_terminal_object C Prod t A) P U D h) (@adjunction_image_func C (@additive_preadditive C Prod t A) t
  (@additive_terminal_object C Prod t A) T0 P Q) (@adjunction_coimage_func C (@additive_preadditive C Prod t A) t
  (@additive_terminal_object C Prod t A) T0 P Q)) (@one_cat_coimage_image_inverse_transf C (@additive_preadditive
  C Prod t A) C1 t (@additive_terminal_object C Prod t A) T0 P Q N)))) (@fapp0 _ _ (@comp_cat_con_fapp1_func B
  (Functor_cat WalkingArrow_cat C) C (@kernel_adjunction_family_boundary_diagram_func B C (@additive_preadditive C
  Prod t A) t (@additive_terminal_object C Prod t A) P U D h) (@adjunction_coimage_func C (@additive_preadditive C
  Prod t A) t (@additive_terminal_object C Prod t A) T0 P Q) (@diagram_evaluation_at_func WalkingArrow_cat C
  walking_arrow_tgt)) (@one_cat_adjunction_coimage_to_target C (@additive_preadditive C Prod t A) C1 t
  (@additive_terminal_object C Prod t A) T0 P Q)) (@comp_fapp0 (Functor_cat B C) (@comp_cat_fapp0 B (Functor_cat
  WalkingArrow_cat C) C (@adjunction_coimage_func C (@additive_preadditive C Prod t A) t
  (@additive_terminal_object C Prod t A) T0 P Q) (@kernel_adjunction_family_boundary_diagram_func B C
  (@additive_preadditive C Prod t A) t (@additive_terminal_object C Prod t A) P U D h)) (@comp_cat_fapp0 B
  (Functor_cat WalkingArrow_cat C) C (@adjunction_image_func C (@additive_preadditive C Prod t A) t
  (@additive_terminal_object C Prod t A) T0 P Q) (@kernel_adjunction_family_boundary_diagram_func B C
  (@additive_preadditive C Prod t A) t (@additive_terminal_object C Prod t A) P U D h))
  (@kernel_adjunction_family_func B C (@additive_preadditive C Prod t A) t (@additive_terminal_object C Prod t A)
  P D) (@kernel_adjunction_family_inclusion_transf B C (@additive_preadditive C Prod t A) t
  (@additive_terminal_object C Prod t A) P (@comp_cat_fapp0 B (Functor_cat WalkingArrow_cat C) (Functor_cat
  WalkingArrow_cat C) (@cokernel_adjunction_arrow_func C (@additive_preadditive C Prod t A) t T0 Q)
  (@kernel_adjunction_family_boundary_diagram_func B C (@additive_preadditive C Prod t A) t
  (@additive_terminal_object C Prod t A) P U D h))) (@fapp0 _ _ (@comp_cat_con_fapp1_func B (Functor_cat
  WalkingArrow_cat C) C (@kernel_adjunction_family_boundary_diagram_func B C (@additive_preadditive C Prod t A) t
  (@additive_terminal_object C Prod t A) P U D h) (@adjunction_coimage_func C (@additive_preadditive C Prod t A) t
  (@additive_terminal_object C Prod t A) T0 P Q) (@adjunction_image_func C (@additive_preadditive C Prod t A) t
  (@additive_terminal_object C Prod t A) T0 P Q)) (@one_cat_coimage_image_comparison C (@additive_preadditive C
  Prod t A) C1 t (@additive_terminal_object C Prod t A) T0 P Q))) (@eq_sym _ _ _ (@eq_trans _ _ _ _ (@eq_ap
  (@Transf B C (@comp_cat_fapp0 B (Functor_cat WalkingArrow_cat C) C (@adjunction_image_func C
  (@additive_preadditive C Prod t A) t (@additive_terminal_object C Prod t A) T0 P Q)
  (@kernel_adjunction_family_boundary_diagram_func B C (@additive_preadditive C Prod t A) t
  (@additive_terminal_object C Prod t A) P U D h)) (@kernel_adjunction_family_func B C (@additive_preadditive C
  Prod t A) t (@additive_terminal_object C Prod t A) P D)) (@Transf B C (@comp_cat_fapp0 B (Functor_cat
  WalkingArrow_cat C) C (@adjunction_coimage_func C (@additive_preadditive C Prod t A) t
  (@additive_terminal_object C Prod t A) T0 P Q) (@kernel_adjunction_family_boundary_diagram_func B C
  (@additive_preadditive C Prod t A) t (@additive_terminal_object C Prod t A) P U D h))
  (@kernel_adjunction_family_func B C (@additive_preadditive C Prod t A) t (@additive_terminal_object C Prod t A)
  P D)) (λ j : τ (@Transf B C (@comp_cat_fapp0 B (Functor_cat WalkingArrow_cat C) C (@adjunction_image_func C
  (@additive_preadditive C Prod t A) t (@additive_terminal_object C Prod t A) T0 P Q)
  (@kernel_adjunction_family_boundary_diagram_func B C (@additive_preadditive C Prod t A) t
  (@additive_terminal_object C Prod t A) P U D h)) (@kernel_adjunction_family_func B C (@additive_preadditive C
  Prod t A) t (@additive_terminal_object C Prod t A) P D)), (@comp_fapp0 (Functor_cat B C) (@comp_cat_fapp0 B
  (Functor_cat WalkingArrow_cat C) C (@adjunction_coimage_func C (@additive_preadditive C Prod t A) t
  (@additive_terminal_object C Prod t A) T0 P Q) (@kernel_adjunction_family_boundary_diagram_func B C
  (@additive_preadditive C Prod t A) t (@additive_terminal_object C Prod t A) P U D h)) (@comp_cat_fapp0 B
  (Functor_cat WalkingArrow_cat C) C (@adjunction_image_func C (@additive_preadditive C Prod t A) t
  (@additive_terminal_object C Prod t A) T0 P Q) (@kernel_adjunction_family_boundary_diagram_func B C
  (@additive_preadditive C Prod t A) t (@additive_terminal_object C Prod t A) P U D h))
  (@kernel_adjunction_family_func B C (@additive_preadditive C Prod t A) t (@additive_terminal_object C Prod t A)
  P D) j (@fapp0 _ _ (@comp_cat_con_fapp1_func B (Functor_cat WalkingArrow_cat C) C
  (@kernel_adjunction_family_boundary_diagram_func B C (@additive_preadditive C Prod t A) t
  (@additive_terminal_object C Prod t A) P U D h) (@adjunction_coimage_func C (@additive_preadditive C Prod t A) t
  (@additive_terminal_object C Prod t A) T0 P Q) (@adjunction_image_func C (@additive_preadditive C Prod t A) t
  (@additive_terminal_object C Prod t A) T0 P Q)) (@one_cat_coimage_image_comparison C (@additive_preadditive C
  Prod t A) C1 t (@additive_terminal_object C Prod t A) T0 P Q)))) (@kernel_adjunction_family_inclusion_transf B C
  (@additive_preadditive C Prod t A) t (@additive_terminal_object C Prod t A) P (@comp_cat_fapp0 B (Functor_cat
  WalkingArrow_cat C) (Functor_cat WalkingArrow_cat C) (@cokernel_adjunction_arrow_func C (@additive_preadditive C
  Prod t A) t T0 Q) (@kernel_adjunction_family_boundary_diagram_func B C (@additive_preadditive C Prod t A) t
  (@additive_terminal_object C Prod t A) P U D h))) (@fapp0 _ _ (@comp_cat_con_fapp1_func B (Functor_cat
  WalkingArrow_cat C) C (@kernel_adjunction_family_boundary_diagram_func B C (@additive_preadditive C Prod t A) t
  (@additive_terminal_object C Prod t A) P U D h) (@adjunction_image_func C (@additive_preadditive C Prod t A) t
  (@additive_terminal_object C Prod t A) T0 P Q) (@diagram_evaluation_at_func WalkingArrow_cat C
  walking_arrow_tgt)) (@adjunction_image_inclusion C (@additive_preadditive C Prod t A) t
  (@additive_terminal_object C Prod t A) T0 P Q)) (@one_cat_image_family_kernel_path B C (@additive_preadditive C
  Prod t A) C1 t (@additive_terminal_object C Prod t A) T0 P Q (@kernel_adjunction_family_boundary_diagram_func B
  C (@additive_preadditive C Prod t A) t (@additive_terminal_object C Prod t A) P U D h)))
  (@one_cat_coimage_target_family_factor_path B C (@additive_preadditive C Prod t A) C1 t
  (@additive_terminal_object C Prod t A) T0 P Q (@kernel_adjunction_family_boundary_diagram_func B C
  (@additive_preadditive C Prod t A) t (@additive_terminal_object C Prod t A) P U D h))))) (@eq_trans _ _ _ _
  (@eq_sym _ _ _ (@comp_assoc (Functor_cat B C) (@comp_cat_fapp0 B (Functor_cat WalkingArrow_cat C) C
  (@adjunction_image_func C (@additive_preadditive C Prod t A) t (@additive_terminal_object C Prod t A) T0 P Q)
  (@kernel_adjunction_family_boundary_diagram_func B C (@additive_preadditive C Prod t A) t
  (@additive_terminal_object C Prod t A) P U D h)) (@comp_cat_fapp0 B (Functor_cat WalkingArrow_cat C) C
  (@adjunction_coimage_func C (@additive_preadditive C Prod t A) t (@additive_terminal_object C Prod t A) T0 P Q)
  (@kernel_adjunction_family_boundary_diagram_func B C (@additive_preadditive C Prod t A) t
  (@additive_terminal_object C Prod t A) P U D h)) (@comp_cat_fapp0 B (Functor_cat WalkingArrow_cat C) C
  (@adjunction_image_func C (@additive_preadditive C Prod t A) t (@additive_terminal_object C Prod t A) T0 P Q)
  (@kernel_adjunction_family_boundary_diagram_func B C (@additive_preadditive C Prod t A) t
  (@additive_terminal_object C Prod t A) P U D h)) (@kernel_adjunction_family_func B C (@additive_preadditive C
  Prod t A) t (@additive_terminal_object C Prod t A) P D) (@kernel_adjunction_family_inclusion_transf B C
  (@additive_preadditive C Prod t A) t (@additive_terminal_object C Prod t A) P (@comp_cat_fapp0 B (Functor_cat
  WalkingArrow_cat C) (Functor_cat WalkingArrow_cat C) (@cokernel_adjunction_arrow_func C (@additive_preadditive C
  Prod t A) t T0 Q) (@kernel_adjunction_family_boundary_diagram_func B C (@additive_preadditive C Prod t A) t
  (@additive_terminal_object C Prod t A) P U D h))) (@fapp0 _ _ (@comp_cat_con_fapp1_func B (Functor_cat
  WalkingArrow_cat C) C (@kernel_adjunction_family_boundary_diagram_func B C (@additive_preadditive C Prod t A) t
  (@additive_terminal_object C Prod t A) P U D h) (@adjunction_coimage_func C (@additive_preadditive C Prod t A) t
  (@additive_terminal_object C Prod t A) T0 P Q) (@adjunction_image_func C (@additive_preadditive C Prod t A) t
  (@additive_terminal_object C Prod t A) T0 P Q)) (@one_cat_coimage_image_comparison C (@additive_preadditive C
  Prod t A) C1 t (@additive_terminal_object C Prod t A) T0 P Q)) (@fapp0 _ _ (@comp_cat_con_fapp1_func B
  (Functor_cat WalkingArrow_cat C) C (@kernel_adjunction_family_boundary_diagram_func B C (@additive_preadditive C
  Prod t A) t (@additive_terminal_object C Prod t A) P U D h) (@adjunction_image_func C (@additive_preadditive C
  Prod t A) t (@additive_terminal_object C Prod t A) T0 P Q) (@adjunction_coimage_func C (@additive_preadditive C
  Prod t A) t (@additive_terminal_object C Prod t A) T0 P Q)) (@one_cat_coimage_image_inverse_transf C
  (@additive_preadditive C Prod t A) C1 t (@additive_terminal_object C Prod t A) T0 P Q N)))) (@eq_ap (@Transf B C
  (@comp_cat_fapp0 B (Functor_cat WalkingArrow_cat C) C (@adjunction_image_func C (@additive_preadditive C Prod t
  A) t (@additive_terminal_object C Prod t A) T0 P Q) (@kernel_adjunction_family_boundary_diagram_func B C
  (@additive_preadditive C Prod t A) t (@additive_terminal_object C Prod t A) P U D h)) (@comp_cat_fapp0 B
  (Functor_cat WalkingArrow_cat C) C (@adjunction_image_func C (@additive_preadditive C Prod t A) t
  (@additive_terminal_object C Prod t A) T0 P Q) (@kernel_adjunction_family_boundary_diagram_func B C
  (@additive_preadditive C Prod t A) t (@additive_terminal_object C Prod t A) P U D h))) (@Transf B C
  (@comp_cat_fapp0 B (Functor_cat WalkingArrow_cat C) C (@adjunction_image_func C (@additive_preadditive C Prod t
  A) t (@additive_terminal_object C Prod t A) T0 P Q) (@kernel_adjunction_family_boundary_diagram_func B C
  (@additive_preadditive C Prod t A) t (@additive_terminal_object C Prod t A) P U D h))
  (@kernel_adjunction_family_func B C (@additive_preadditive C Prod t A) t (@additive_terminal_object C Prod t A)
  P D)) (λ j : τ (@Transf B C (@comp_cat_fapp0 B (Functor_cat WalkingArrow_cat C) C (@adjunction_image_func C
  (@additive_preadditive C Prod t A) t (@additive_terminal_object C Prod t A) T0 P Q)
  (@kernel_adjunction_family_boundary_diagram_func B C (@additive_preadditive C Prod t A) t
  (@additive_terminal_object C Prod t A) P U D h)) (@comp_cat_fapp0 B (Functor_cat WalkingArrow_cat C) C
  (@adjunction_image_func C (@additive_preadditive C Prod t A) t (@additive_terminal_object C Prod t A) T0 P Q)
  (@kernel_adjunction_family_boundary_diagram_func B C (@additive_preadditive C Prod t A) t
  (@additive_terminal_object C Prod t A) P U D h))), (@comp_fapp0 (Functor_cat B C) (@comp_cat_fapp0 B
  (Functor_cat WalkingArrow_cat C) C (@adjunction_image_func C (@additive_preadditive C Prod t A) t
  (@additive_terminal_object C Prod t A) T0 P Q) (@kernel_adjunction_family_boundary_diagram_func B C
  (@additive_preadditive C Prod t A) t (@additive_terminal_object C Prod t A) P U D h)) (@comp_cat_fapp0 B
  (Functor_cat WalkingArrow_cat C) C (@adjunction_image_func C (@additive_preadditive C Prod t A) t
  (@additive_terminal_object C Prod t A) T0 P Q) (@kernel_adjunction_family_boundary_diagram_func B C
  (@additive_preadditive C Prod t A) t (@additive_terminal_object C Prod t A) P U D h))
  (@kernel_adjunction_family_func B C (@additive_preadditive C Prod t A) t (@additive_terminal_object C Prod t A)
  P D) (@kernel_adjunction_family_inclusion_transf B C (@additive_preadditive C Prod t A) t
  (@additive_terminal_object C Prod t A) P (@comp_cat_fapp0 B (Functor_cat WalkingArrow_cat C) (Functor_cat
  WalkingArrow_cat C) (@cokernel_adjunction_arrow_func C (@additive_preadditive C Prod t A) t T0 Q)
  (@kernel_adjunction_family_boundary_diagram_func B C (@additive_preadditive C Prod t A) t
  (@additive_terminal_object C Prod t A) P U D h))) j)) (@comp_fapp0 (Functor_cat B C) (@comp_cat_fapp0 B
  (Functor_cat WalkingArrow_cat C) C (@adjunction_image_func C (@additive_preadditive C Prod t A) t
  (@additive_terminal_object C Prod t A) T0 P Q) (@kernel_adjunction_family_boundary_diagram_func B C
  (@additive_preadditive C Prod t A) t (@additive_terminal_object C Prod t A) P U D h)) (@comp_cat_fapp0 B
  (Functor_cat WalkingArrow_cat C) C (@adjunction_coimage_func C (@additive_preadditive C Prod t A) t
  (@additive_terminal_object C Prod t A) T0 P Q) (@kernel_adjunction_family_boundary_diagram_func B C
  (@additive_preadditive C Prod t A) t (@additive_terminal_object C Prod t A) P U D h)) (@comp_cat_fapp0 B
  (Functor_cat WalkingArrow_cat C) C (@adjunction_image_func C (@additive_preadditive C Prod t A) t
  (@additive_terminal_object C Prod t A) T0 P Q) (@kernel_adjunction_family_boundary_diagram_func B C
  (@additive_preadditive C Prod t A) t (@additive_terminal_object C Prod t A) P U D h)) (@fapp0 _ _
  (@comp_cat_con_fapp1_func B (Functor_cat WalkingArrow_cat C) C (@kernel_adjunction_family_boundary_diagram_func
  B C (@additive_preadditive C Prod t A) t (@additive_terminal_object C Prod t A) P U D h)
  (@adjunction_coimage_func C (@additive_preadditive C Prod t A) t (@additive_terminal_object C Prod t A) T0 P Q)
  (@adjunction_image_func C (@additive_preadditive C Prod t A) t (@additive_terminal_object C Prod t A) T0 P Q))
  (@one_cat_coimage_image_comparison C (@additive_preadditive C Prod t A) C1 t (@additive_terminal_object C Prod t
  A) T0 P Q)) (@fapp0 _ _ (@comp_cat_con_fapp1_func B (Functor_cat WalkingArrow_cat C) C
  (@kernel_adjunction_family_boundary_diagram_func B C (@additive_preadditive C Prod t A) t
  (@additive_terminal_object C Prod t A) P U D h) (@adjunction_image_func C (@additive_preadditive C Prod t A) t
  (@additive_terminal_object C Prod t A) T0 P Q) (@adjunction_coimage_func C (@additive_preadditive C Prod t A) t
  (@additive_terminal_object C Prod t A) T0 P Q)) (@one_cat_coimage_image_inverse_transf C (@additive_preadditive
  C Prod t A) C1 t (@additive_terminal_object C Prod t A) T0 P Q N))) (@id (Functor_cat B C) (@comp_cat_fapp0 B
  (Functor_cat WalkingArrow_cat C) C (@adjunction_image_func C (@additive_preadditive C Prod t A) t
  (@additive_terminal_object C Prod t A) T0 P Q) (@kernel_adjunction_family_boundary_diagram_func B C
  (@additive_preadditive C Prod t A) t (@additive_terminal_object C Prod t A) P U D h)))
  (@omega_equiv_left_as_right_law (Functor_cat B C) (@comp_cat_fapp0 B (Functor_cat WalkingArrow_cat C) C
  (@adjunction_coimage_func C (@additive_preadditive C Prod t A) t (@additive_terminal_object C Prod t A) T0 P Q)
  (@kernel_adjunction_family_boundary_diagram_func B C (@additive_preadditive C Prod t A) t
  (@additive_terminal_object C Prod t A) P U D h)) (@comp_cat_fapp0 B (Functor_cat WalkingArrow_cat C) C
  (@adjunction_image_func C (@additive_preadditive C Prod t A) t (@additive_terminal_object C Prod t A) T0 P Q)
  (@kernel_adjunction_family_boundary_diagram_func B C (@additive_preadditive C Prod t A) t
  (@additive_terminal_object C Prod t A) P U D h)) (@fapp0 _ _ (@comp_cat_con_fapp1_func B (Functor_cat
  WalkingArrow_cat C) C (@kernel_adjunction_family_boundary_diagram_func B C (@additive_preadditive C Prod t A) t
  (@additive_terminal_object C Prod t A) P U D h) (@adjunction_coimage_func C (@additive_preadditive C Prod t A) t
  (@additive_terminal_object C Prod t A) T0 P Q) (@adjunction_image_func C (@additive_preadditive C Prod t A) t
  (@additive_terminal_object C Prod t A) T0 P Q)) (@one_cat_coimage_image_comparison C (@additive_preadditive C
  Prod t A) C1 t (@additive_terminal_object C Prod t A) T0 P Q)) (@one_cat_adjunction_normality_family B C
  (@additive_preadditive C Prod t A) C1 t (@additive_terminal_object C Prod t A) T0 P Q N
  (@kernel_adjunction_family_boundary_diagram_func B C (@additive_preadditive C Prod t A) t
  (@additive_terminal_object C Prod t A) P U D h))))))) (@one_cat_boundary_image_lift_reconstruction B C C1
  Prod t A T0 P Q N U D h X v z)));

// The original difference kernel is the whole boundary-representative parameter object.
symbol one_cat_boundary_representative_func [B C : Cat] (C1 : τ (IsNCat (cat_succ cat_zero) C)) [Prod : τ
  (Functor (Product_cat C C) C)] [t : τ (Obj C)] (A : τ (@AdditiveCategory C Prod t)) (T0 : τ (@TerminalObject
  (Op_cat C) t)) (P : τ (@KernelAdjunctionStructure C (@additive_preadditive C Prod t A) t
  (@additive_terminal_object C Prod t A))) (Q : τ (@CokernelAdjunctionStructure C (@additive_preadditive C Prod t
  A) t T0)) (N : τ (@OneCatAdjunctionNormality C (@additive_preadditive C Prod t A) C1 t
  (@additive_terminal_object C Prod t A) T0 P Q)) (U : τ (Functor B C)) (D : τ (Functor B (Functor_cat
  WalkingArrow_cat C))) (h : τ (@Transf B (Functor_cat WalkingArrow_cat C) (@comp_cat_fapp0 B C (Functor_cat
  WalkingArrow_cat C) (@terminal_arrow_diagram_func C t (@additive_terminal_object C Prod t A)) U) D)) (X : τ
  (Functor B C)) (v : τ (@Transf B C X (@kernel_adjunction_family_func B C (@additive_preadditive C Prod t A) t
  (@additive_terminal_object C Prod t A) P D))) (z : τ (@= (@Transf B C X (@homology_adjunction_family_func B C
  (@additive_preadditive C Prod t A) t (@additive_terminal_object C Prod t A) T0 P Q U D h)) (@comp_fapp0
  (Functor_cat B C) X (@kernel_adjunction_family_func B C (@additive_preadditive C Prod t A) t
  (@additive_terminal_object C Prod t A) P D) (@homology_adjunction_family_func B C (@additive_preadditive C Prod
  t A) t (@additive_terminal_object C Prod t A) T0 P Q U D h) (@homology_adjunction_family_projection_transf B C
  (@additive_preadditive C Prod t A) t (@additive_terminal_object C Prod t A) T0 P Q U D h) v)
  (@zero_arrow_family_zero_transf B C t (@additive_terminal_object C Prod t A) T0 X
  (@homology_adjunction_family_func B C (@additive_preadditive C Prod t A) t (@additive_terminal_object C Prod t
  A) T0 P Q U D h))))
 : τ (Functor B C)
≔ (@kernel_adjunction_family_func B C (@additive_preadditive C Prod t A) t (@additive_terminal_object C Prod t A)
  P (@transf_arrow_diagram_func B C (@fapp0 (Functor_cat B (Product_cat C C)) (Functor_cat B C)
  (@comp_cat_cov_func B (Product_cat C C) C Prod) (@Struct_sigma (Functor B C) (λ _ : τ (Functor B C), Functor B
  C) X U)) (@comp_cat_fapp0 B (Functor_cat WalkingArrow_cat C) C (@adjunction_coimage_func C
  (@additive_preadditive C Prod t A) t (@additive_terminal_object C Prod t A) T0 P Q)
  (@kernel_adjunction_family_boundary_diagram_func B C (@additive_preadditive C Prod t A) t
  (@additive_terminal_object C Prod t A) P U D h)) (@one_cat_difference_cospan_transf B C C1 Prod t A T0 X U
  (@comp_cat_fapp0 B (Functor_cat WalkingArrow_cat C) C (@adjunction_coimage_func C (@additive_preadditive C Prod
  t A) t (@additive_terminal_object C Prod t A) T0 P Q) (@kernel_adjunction_family_boundary_diagram_func B C
  (@additive_preadditive C Prod t A) t (@additive_terminal_object C Prod t A) P U D h))
  (@one_cat_boundary_coimage_lift B C C1 Prod t A T0 P Q N U D h X v z)
  (@cokernel_adjunction_family_projection_transf B C (@additive_preadditive C Prod t A) t T0 Q (@comp_cat_fapp0 B
  (Functor_cat WalkingArrow_cat C) (Functor_cat WalkingArrow_cat C) (@kernel_adjunction_arrow_func C
  (@additive_preadditive C Prod t A) t (@additive_terminal_object C Prod t A) P)
  (@kernel_adjunction_family_boundary_diagram_func B C (@additive_preadditive C Prod t A) t
  (@additive_terminal_object C Prod t A) P U D h))))));

// The original difference-kernel first projection covers the original source.
symbol one_cat_boundary_representative_projection [B C : Cat] (C1 : τ (IsNCat (cat_succ cat_zero) C)) [Prod
  : τ (Functor (Product_cat C C) C)] [t : τ (Obj C)] (A : τ (@AdditiveCategory C Prod t)) (T0 : τ (@TerminalObject
  (Op_cat C) t)) (P : τ (@KernelAdjunctionStructure C (@additive_preadditive C Prod t A) t
  (@additive_terminal_object C Prod t A))) (Q : τ (@CokernelAdjunctionStructure C (@additive_preadditive C Prod t
  A) t T0)) (N : τ (@OneCatAdjunctionNormality C (@additive_preadditive C Prod t A) C1 t
  (@additive_terminal_object C Prod t A) T0 P Q)) (U : τ (Functor B C)) (D : τ (Functor B (Functor_cat
  WalkingArrow_cat C))) (h : τ (@Transf B (Functor_cat WalkingArrow_cat C) (@comp_cat_fapp0 B C (Functor_cat
  WalkingArrow_cat C) (@terminal_arrow_diagram_func C t (@additive_terminal_object C Prod t A)) U) D)) (X : τ
  (Functor B C)) (v : τ (@Transf B C X (@kernel_adjunction_family_func B C (@additive_preadditive C Prod t A) t
  (@additive_terminal_object C Prod t A) P D))) (z : τ (@= (@Transf B C X (@homology_adjunction_family_func B C
  (@additive_preadditive C Prod t A) t (@additive_terminal_object C Prod t A) T0 P Q U D h)) (@comp_fapp0
  (Functor_cat B C) X (@kernel_adjunction_family_func B C (@additive_preadditive C Prod t A) t
  (@additive_terminal_object C Prod t A) P D) (@homology_adjunction_family_func B C (@additive_preadditive C Prod
  t A) t (@additive_terminal_object C Prod t A) T0 P Q U D h) (@homology_adjunction_family_projection_transf B C
  (@additive_preadditive C Prod t A) t (@additive_terminal_object C Prod t A) T0 P Q U D h) v)
  (@zero_arrow_family_zero_transf B C t (@additive_terminal_object C Prod t A) T0 X
  (@homology_adjunction_family_func B C (@additive_preadditive C Prod t A) t (@additive_terminal_object C Prod t
  A) T0 P Q U D h))))
 : τ (@Transf B C (@kernel_adjunction_family_func B C (@additive_preadditive C Prod t A) t
  (@additive_terminal_object C Prod t A) P (@transf_arrow_diagram_func B C (@fapp0 (Functor_cat B (Product_cat C
  C)) (Functor_cat B C) (@comp_cat_cov_func B (Product_cat C C) C Prod) (@Struct_sigma (Functor B C) (λ _ : τ
  (Functor B C), Functor B C) X U)) (@comp_cat_fapp0 B (Functor_cat WalkingArrow_cat C) C
  (@adjunction_coimage_func C (@additive_preadditive C Prod t A) t (@additive_terminal_object C Prod t A) T0 P Q)
  (@kernel_adjunction_family_boundary_diagram_func B C (@additive_preadditive C Prod t A) t
  (@additive_terminal_object C Prod t A) P U D h)) (@one_cat_difference_cospan_transf B C C1 Prod t A T0 X U
  (@comp_cat_fapp0 B (Functor_cat WalkingArrow_cat C) C (@adjunction_coimage_func C (@additive_preadditive C Prod
  t A) t (@additive_terminal_object C Prod t A) T0 P Q) (@kernel_adjunction_family_boundary_diagram_func B C
  (@additive_preadditive C Prod t A) t (@additive_terminal_object C Prod t A) P U D h))
  (@one_cat_boundary_coimage_lift B C C1 Prod t A T0 P Q N U D h X v z)
  (@cokernel_adjunction_family_projection_transf B C (@additive_preadditive C Prod t A) t T0 Q (@comp_cat_fapp0 B
  (Functor_cat WalkingArrow_cat C) (Functor_cat WalkingArrow_cat C) (@kernel_adjunction_arrow_func C
  (@additive_preadditive C Prod t A) t (@additive_terminal_object C Prod t A) P)
  (@kernel_adjunction_family_boundary_diagram_func B C (@additive_preadditive C Prod t A) t
  (@additive_terminal_object C Prod t A) P U D h)))))) X)
≔ @one_cat_cospan_kernel_first B C C1 Prod t A T0 P Q X U (@comp_cat_fapp0 B (Functor_cat WalkingArrow_cat
  C) C (@adjunction_coimage_func C (@additive_preadditive C Prod t A) t (@additive_terminal_object C Prod t A) T0
  P Q) (@kernel_adjunction_family_boundary_diagram_func B C (@additive_preadditive C Prod t A) t
  (@additive_terminal_object C Prod t A) P U D h)) (@one_cat_boundary_coimage_lift B C C1 Prod t A T0 P Q N
  U D h X v z) (@cokernel_adjunction_family_projection_transf B C (@additive_preadditive C Prod t A) t T0 Q
  (@comp_cat_fapp0 B (Functor_cat WalkingArrow_cat C) (Functor_cat WalkingArrow_cat C)
  (@kernel_adjunction_arrow_func C (@additive_preadditive C Prod t A) t (@additive_terminal_object C Prod t A) P)
  (@kernel_adjunction_family_boundary_diagram_func B C (@additive_preadditive C Prod t A) t
  (@additive_terminal_object C Prod t A) P U D h)));

// The original second projection is the whole boundary representative.
symbol one_cat_boundary_representative_map [B C : Cat] (C1 : τ (IsNCat (cat_succ cat_zero) C)) [Prod : τ
  (Functor (Product_cat C C) C)] [t : τ (Obj C)] (A : τ (@AdditiveCategory C Prod t)) (T0 : τ (@TerminalObject
  (Op_cat C) t)) (P : τ (@KernelAdjunctionStructure C (@additive_preadditive C Prod t A) t
  (@additive_terminal_object C Prod t A))) (Q : τ (@CokernelAdjunctionStructure C (@additive_preadditive C Prod t
  A) t T0)) (N : τ (@OneCatAdjunctionNormality C (@additive_preadditive C Prod t A) C1 t
  (@additive_terminal_object C Prod t A) T0 P Q)) (U : τ (Functor B C)) (D : τ (Functor B (Functor_cat
  WalkingArrow_cat C))) (h : τ (@Transf B (Functor_cat WalkingArrow_cat C) (@comp_cat_fapp0 B C (Functor_cat
  WalkingArrow_cat C) (@terminal_arrow_diagram_func C t (@additive_terminal_object C Prod t A)) U) D)) (X : τ
  (Functor B C)) (v : τ (@Transf B C X (@kernel_adjunction_family_func B C (@additive_preadditive C Prod t A) t
  (@additive_terminal_object C Prod t A) P D))) (z : τ (@= (@Transf B C X (@homology_adjunction_family_func B C
  (@additive_preadditive C Prod t A) t (@additive_terminal_object C Prod t A) T0 P Q U D h)) (@comp_fapp0
  (Functor_cat B C) X (@kernel_adjunction_family_func B C (@additive_preadditive C Prod t A) t
  (@additive_terminal_object C Prod t A) P D) (@homology_adjunction_family_func B C (@additive_preadditive C Prod
  t A) t (@additive_terminal_object C Prod t A) T0 P Q U D h) (@homology_adjunction_family_projection_transf B C
  (@additive_preadditive C Prod t A) t (@additive_terminal_object C Prod t A) T0 P Q U D h) v)
  (@zero_arrow_family_zero_transf B C t (@additive_terminal_object C Prod t A) T0 X
  (@homology_adjunction_family_func B C (@additive_preadditive C Prod t A) t (@additive_terminal_object C Prod t
  A) T0 P Q U D h))))
 : τ (@Transf B C (@kernel_adjunction_family_func B C (@additive_preadditive C Prod t A) t
  (@additive_terminal_object C Prod t A) P (@transf_arrow_diagram_func B C (@fapp0 (Functor_cat B (Product_cat C
  C)) (Functor_cat B C) (@comp_cat_cov_func B (Product_cat C C) C Prod) (@Struct_sigma (Functor B C) (λ _ : τ
  (Functor B C), Functor B C) X U)) (@comp_cat_fapp0 B (Functor_cat WalkingArrow_cat C) C
  (@adjunction_coimage_func C (@additive_preadditive C Prod t A) t (@additive_terminal_object C Prod t A) T0 P Q)
  (@kernel_adjunction_family_boundary_diagram_func B C (@additive_preadditive C Prod t A) t
  (@additive_terminal_object C Prod t A) P U D h)) (@one_cat_difference_cospan_transf B C C1 Prod t A T0 X U
  (@comp_cat_fapp0 B (Functor_cat WalkingArrow_cat C) C (@adjunction_coimage_func C (@additive_preadditive C Prod
  t A) t (@additive_terminal_object C Prod t A) T0 P Q) (@kernel_adjunction_family_boundary_diagram_func B C
  (@additive_preadditive C Prod t A) t (@additive_terminal_object C Prod t A) P U D h))
  (@one_cat_boundary_coimage_lift B C C1 Prod t A T0 P Q N U D h X v z)
  (@cokernel_adjunction_family_projection_transf B C (@additive_preadditive C Prod t A) t T0 Q (@comp_cat_fapp0 B
  (Functor_cat WalkingArrow_cat C) (Functor_cat WalkingArrow_cat C) (@kernel_adjunction_arrow_func C
  (@additive_preadditive C Prod t A) t (@additive_terminal_object C Prod t A) P)
  (@kernel_adjunction_family_boundary_diagram_func B C (@additive_preadditive C Prod t A) t
  (@additive_terminal_object C Prod t A) P U D h)))))) U)
≔ @one_cat_cospan_kernel_second B C C1 Prod t A T0 P Q X U (@comp_cat_fapp0 B (Functor_cat WalkingArrow_cat
  C) C (@adjunction_coimage_func C (@additive_preadditive C Prod t A) t (@additive_terminal_object C Prod t A) T0
  P Q) (@kernel_adjunction_family_boundary_diagram_func B C (@additive_preadditive C Prod t A) t
  (@additive_terminal_object C Prod t A) P U D h)) (@one_cat_boundary_coimage_lift B C C1 Prod t A T0 P Q N
  U D h X v z) (@cokernel_adjunction_family_projection_transf B C (@additive_preadditive C Prod t A) t T0 Q
  (@comp_cat_fapp0 B (Functor_cat WalkingArrow_cat C) (Functor_cat WalkingArrow_cat C)
  (@kernel_adjunction_arrow_func C (@additive_preadditive C Prod t A) t (@additive_terminal_object C Prod t A) P)
  (@kernel_adjunction_family_boundary_diagram_func B C (@additive_preadditive C Prod t A) t
  (@additive_terminal_object C Prod t A) P U D h)));

// The original whole boundary reconstructs the original cycle after the derived cover.
symbol one_cat_boundary_representative_path [B C : Cat] (C1 : τ (IsNCat (cat_succ cat_zero) C)) [Prod : τ
  (Functor (Product_cat C C) C)] [t : τ (Obj C)] (A : τ (@AdditiveCategory C Prod t)) (T0 : τ (@TerminalObject
  (Op_cat C) t)) (P : τ (@KernelAdjunctionStructure C (@additive_preadditive C Prod t A) t
  (@additive_terminal_object C Prod t A))) (Q : τ (@CokernelAdjunctionStructure C (@additive_preadditive C Prod t
  A) t T0)) (N : τ (@OneCatAdjunctionNormality C (@additive_preadditive C Prod t A) C1 t
  (@additive_terminal_object C Prod t A) T0 P Q)) (U : τ (Functor B C)) (D : τ (Functor B (Functor_cat
  WalkingArrow_cat C))) (h : τ (@Transf B (Functor_cat WalkingArrow_cat C) (@comp_cat_fapp0 B C (Functor_cat
  WalkingArrow_cat C) (@terminal_arrow_diagram_func C t (@additive_terminal_object C Prod t A)) U) D)) (X : τ
  (Functor B C)) (v : τ (@Transf B C X (@kernel_adjunction_family_func B C (@additive_preadditive C Prod t A) t
  (@additive_terminal_object C Prod t A) P D))) (z : τ (@= (@Transf B C X (@homology_adjunction_family_func B C
  (@additive_preadditive C Prod t A) t (@additive_terminal_object C Prod t A) T0 P Q U D h)) (@comp_fapp0
  (Functor_cat B C) X (@kernel_adjunction_family_func B C (@additive_preadditive C Prod t A) t
  (@additive_terminal_object C Prod t A) P D) (@homology_adjunction_family_func B C (@additive_preadditive C Prod
  t A) t (@additive_terminal_object C Prod t A) T0 P Q U D h) (@homology_adjunction_family_projection_transf B C
  (@additive_preadditive C Prod t A) t (@additive_terminal_object C Prod t A) T0 P Q U D h) v)
  (@zero_arrow_family_zero_transf B C t (@additive_terminal_object C Prod t A) T0 X
  (@homology_adjunction_family_func B C (@additive_preadditive C Prod t A) t (@additive_terminal_object C Prod t
  A) T0 P Q U D h))))
 : τ (@= (@Transf B C (@kernel_adjunction_family_func B C (@additive_preadditive C Prod t A) t
  (@additive_terminal_object C Prod t A) P (@transf_arrow_diagram_func B C (@fapp0 (Functor_cat B (Product_cat C
  C)) (Functor_cat B C) (@comp_cat_cov_func B (Product_cat C C) C Prod) (@Struct_sigma (Functor B C) (λ _ : τ
  (Functor B C), Functor B C) X U)) (@comp_cat_fapp0 B (Functor_cat WalkingArrow_cat C) C
  (@adjunction_coimage_func C (@additive_preadditive C Prod t A) t (@additive_terminal_object C Prod t A) T0 P Q)
  (@kernel_adjunction_family_boundary_diagram_func B C (@additive_preadditive C Prod t A) t
  (@additive_terminal_object C Prod t A) P U D h)) (@one_cat_difference_cospan_transf B C C1 Prod t A T0 X U
  (@comp_cat_fapp0 B (Functor_cat WalkingArrow_cat C) C (@adjunction_coimage_func C (@additive_preadditive C Prod
  t A) t (@additive_terminal_object C Prod t A) T0 P Q) (@kernel_adjunction_family_boundary_diagram_func B C
  (@additive_preadditive C Prod t A) t (@additive_terminal_object C Prod t A) P U D h))
  (@one_cat_boundary_coimage_lift B C C1 Prod t A T0 P Q N U D h X v z)
  (@cokernel_adjunction_family_projection_transf B C (@additive_preadditive C Prod t A) t T0 Q (@comp_cat_fapp0 B
  (Functor_cat WalkingArrow_cat C) (Functor_cat WalkingArrow_cat C) (@kernel_adjunction_arrow_func C
  (@additive_preadditive C Prod t A) t (@additive_terminal_object C Prod t A) P)
  (@kernel_adjunction_family_boundary_diagram_func B C (@additive_preadditive C Prod t A) t
  (@additive_terminal_object C Prod t A) P U D h)))))) (@kernel_adjunction_family_func B C (@additive_preadditive
  C Prod t A) t (@additive_terminal_object C Prod t A) P D)) (@comp_fapp0 (Functor_cat B C)
  (@kernel_adjunction_family_func B C (@additive_preadditive C Prod t A) t (@additive_terminal_object C Prod t A)
  P (@transf_arrow_diagram_func B C (@fapp0 (Functor_cat B (Product_cat C C)) (Functor_cat B C)
  (@comp_cat_cov_func B (Product_cat C C) C Prod) (@Struct_sigma (Functor B C) (λ _ : τ (Functor B C), Functor B
  C) X U)) (@comp_cat_fapp0 B (Functor_cat WalkingArrow_cat C) C (@adjunction_coimage_func C
  (@additive_preadditive C Prod t A) t (@additive_terminal_object C Prod t A) T0 P Q)
  (@kernel_adjunction_family_boundary_diagram_func B C (@additive_preadditive C Prod t A) t
  (@additive_terminal_object C Prod t A) P U D h)) (@one_cat_difference_cospan_transf B C C1 Prod t A T0 X U
  (@comp_cat_fapp0 B (Functor_cat WalkingArrow_cat C) C (@adjunction_coimage_func C (@additive_preadditive C Prod
  t A) t (@additive_terminal_object C Prod t A) T0 P Q) (@kernel_adjunction_family_boundary_diagram_func B C
  (@additive_preadditive C Prod t A) t (@additive_terminal_object C Prod t A) P U D h))
  (@one_cat_boundary_coimage_lift B C C1 Prod t A T0 P Q N U D h X v z)
  (@cokernel_adjunction_family_projection_transf B C (@additive_preadditive C Prod t A) t T0 Q (@comp_cat_fapp0 B
  (Functor_cat WalkingArrow_cat C) (Functor_cat WalkingArrow_cat C) (@kernel_adjunction_arrow_func C
  (@additive_preadditive C Prod t A) t (@additive_terminal_object C Prod t A) P)
  (@kernel_adjunction_family_boundary_diagram_func B C (@additive_preadditive C Prod t A) t
  (@additive_terminal_object C Prod t A) P U D h)))))) U (@kernel_adjunction_family_func B C
  (@additive_preadditive C Prod t A) t (@additive_terminal_object C Prod t A) P D)
  (@kernel_adjunction_family_boundary_transf B C (@additive_preadditive C Prod t A) t (@additive_terminal_object C
  Prod t A) P U D h) (@one_cat_boundary_representative_map B C C1 Prod t A T0 P Q N U D h X v z))
  (@comp_fapp0 (Functor_cat B C) (@kernel_adjunction_family_func B C (@additive_preadditive C Prod t A) t
  (@additive_terminal_object C Prod t A) P (@transf_arrow_diagram_func B C (@fapp0 (Functor_cat B (Product_cat C
  C)) (Functor_cat B C) (@comp_cat_cov_func B (Product_cat C C) C Prod) (@Struct_sigma (Functor B C) (λ _ : τ
  (Functor B C), Functor B C) X U)) (@comp_cat_fapp0 B (Functor_cat WalkingArrow_cat C) C
  (@adjunction_coimage_func C (@additive_preadditive C Prod t A) t (@additive_terminal_object C Prod t A) T0 P Q)
  (@kernel_adjunction_family_boundary_diagram_func B C (@additive_preadditive C Prod t A) t
  (@additive_terminal_object C Prod t A) P U D h)) (@one_cat_difference_cospan_transf B C C1 Prod t A T0 X U
  (@comp_cat_fapp0 B (Functor_cat WalkingArrow_cat C) C (@adjunction_coimage_func C (@additive_preadditive C Prod
  t A) t (@additive_terminal_object C Prod t A) T0 P Q) (@kernel_adjunction_family_boundary_diagram_func B C
  (@additive_preadditive C Prod t A) t (@additive_terminal_object C Prod t A) P U D h))
  (@one_cat_boundary_coimage_lift B C C1 Prod t A T0 P Q N U D h X v z)
  (@cokernel_adjunction_family_projection_transf B C (@additive_preadditive C Prod t A) t T0 Q (@comp_cat_fapp0 B
  (Functor_cat WalkingArrow_cat C) (Functor_cat WalkingArrow_cat C) (@kernel_adjunction_arrow_func C
  (@additive_preadditive C Prod t A) t (@additive_terminal_object C Prod t A) P)
  (@kernel_adjunction_family_boundary_diagram_func B C (@additive_preadditive C Prod t A) t
  (@additive_terminal_object C Prod t A) P U D h)))))) X (@kernel_adjunction_family_func B C
  (@additive_preadditive C Prod t A) t (@additive_terminal_object C Prod t A) P D) v
  (@one_cat_boundary_representative_projection B C C1 Prod t A T0 P Q N U D h X v z)))
≔ (@eq_trans _ _ _ _ (@eq_ap (@Transf B C U (@kernel_adjunction_family_func B C (@additive_preadditive C Prod t A)
  t (@additive_terminal_object C Prod t A) P D)) (@Transf B C (@kernel_adjunction_family_func B C
  (@additive_preadditive C Prod t A) t (@additive_terminal_object C Prod t A) P (@transf_arrow_diagram_func B C
  (@fapp0 (Functor_cat B (Product_cat C C)) (Functor_cat B C) (@comp_cat_cov_func B (Product_cat C C) C Prod)
  (@Struct_sigma (Functor B C) (λ _ : τ (Functor B C), Functor B C) X U)) (@comp_cat_fapp0 B (Functor_cat
  WalkingArrow_cat C) C (@adjunction_coimage_func C (@additive_preadditive C Prod t A) t
  (@additive_terminal_object C Prod t A) T0 P Q) (@kernel_adjunction_family_boundary_diagram_func B C
  (@additive_preadditive C Prod t A) t (@additive_terminal_object C Prod t A) P U D h))
  (@one_cat_difference_cospan_transf B C C1 Prod t A T0 X U (@comp_cat_fapp0 B (Functor_cat WalkingArrow_cat C) C
  (@adjunction_coimage_func C (@additive_preadditive C Prod t A) t (@additive_terminal_object C Prod t A) T0 P Q)
  (@kernel_adjunction_family_boundary_diagram_func B C (@additive_preadditive C Prod t A) t
  (@additive_terminal_object C Prod t A) P U D h)) (@one_cat_boundary_coimage_lift B C C1 Prod t A T0 P Q N
  U D h X v z) (@cokernel_adjunction_family_projection_transf B C (@additive_preadditive C Prod t A) t T0 Q
  (@comp_cat_fapp0 B (Functor_cat WalkingArrow_cat C) (Functor_cat WalkingArrow_cat C)
  (@kernel_adjunction_arrow_func C (@additive_preadditive C Prod t A) t (@additive_terminal_object C Prod t A) P)
  (@kernel_adjunction_family_boundary_diagram_func B C (@additive_preadditive C Prod t A) t
  (@additive_terminal_object C Prod t A) P U D h)))))) (@kernel_adjunction_family_func B C (@additive_preadditive
  C Prod t A) t (@additive_terminal_object C Prod t A) P D)) (λ j : τ (@Transf B C U
  (@kernel_adjunction_family_func B C (@additive_preadditive C Prod t A) t (@additive_terminal_object C Prod t A)
  P D)), (@comp_fapp0 (Functor_cat B C) (@kernel_adjunction_family_func B C (@additive_preadditive C Prod t A) t
  (@additive_terminal_object C Prod t A) P (@transf_arrow_diagram_func B C (@fapp0 (Functor_cat B (Product_cat C
  C)) (Functor_cat B C) (@comp_cat_cov_func B (Product_cat C C) C Prod) (@Struct_sigma (Functor B C) (λ _ : τ
  (Functor B C), Functor B C) X U)) (@comp_cat_fapp0 B (Functor_cat WalkingArrow_cat C) C
  (@adjunction_coimage_func C (@additive_preadditive C Prod t A) t (@additive_terminal_object C Prod t A) T0 P Q)
  (@kernel_adjunction_family_boundary_diagram_func B C (@additive_preadditive C Prod t A) t
  (@additive_terminal_object C Prod t A) P U D h)) (@one_cat_difference_cospan_transf B C C1 Prod t A T0 X U
  (@comp_cat_fapp0 B (Functor_cat WalkingArrow_cat C) C (@adjunction_coimage_func C (@additive_preadditive C Prod
  t A) t (@additive_terminal_object C Prod t A) T0 P Q) (@kernel_adjunction_family_boundary_diagram_func B C
  (@additive_preadditive C Prod t A) t (@additive_terminal_object C Prod t A) P U D h))
  (@one_cat_boundary_coimage_lift B C C1 Prod t A T0 P Q N U D h X v z)
  (@cokernel_adjunction_family_projection_transf B C (@additive_preadditive C Prod t A) t T0 Q (@comp_cat_fapp0 B
  (Functor_cat WalkingArrow_cat C) (Functor_cat WalkingArrow_cat C) (@kernel_adjunction_arrow_func C
  (@additive_preadditive C Prod t A) t (@additive_terminal_object C Prod t A) P)
  (@kernel_adjunction_family_boundary_diagram_func B C (@additive_preadditive C Prod t A) t
  (@additive_terminal_object C Prod t A) P U D h)))))) U (@kernel_adjunction_family_func B C
  (@additive_preadditive C Prod t A) t (@additive_terminal_object C Prod t A) P D) j
  (@one_cat_boundary_representative_map B C C1 Prod t A T0 P Q N U D h X v z)))
  (@kernel_adjunction_family_boundary_transf B C (@additive_preadditive C Prod t A) t (@additive_terminal_object C
  Prod t A) P U D h) (@comp_fapp0 (Functor_cat B C) U (@comp_cat_fapp0 B (Functor_cat WalkingArrow_cat C) C
  (@adjunction_coimage_func C (@additive_preadditive C Prod t A) t (@additive_terminal_object C Prod t A) T0 P Q)
  (@kernel_adjunction_family_boundary_diagram_func B C (@additive_preadditive C Prod t A) t
  (@additive_terminal_object C Prod t A) P U D h)) (@kernel_adjunction_family_func B C (@additive_preadditive C
  Prod t A) t (@additive_terminal_object C Prod t A) P D) (@fapp0 _ _ (@comp_cat_con_fapp1_func B (Functor_cat
  WalkingArrow_cat C) C (@kernel_adjunction_family_boundary_diagram_func B C (@additive_preadditive C Prod t A) t
  (@additive_terminal_object C Prod t A) P U D h) (@adjunction_coimage_func C (@additive_preadditive C Prod t A) t
  (@additive_terminal_object C Prod t A) T0 P Q) (@diagram_evaluation_at_func WalkingArrow_cat C
  walking_arrow_tgt)) (@one_cat_adjunction_coimage_to_target C (@additive_preadditive C Prod t A) C1 t
  (@additive_terminal_object C Prod t A) T0 P Q)) (@cokernel_adjunction_family_projection_transf B C
  (@additive_preadditive C Prod t A) t T0 Q (@comp_cat_fapp0 B (Functor_cat WalkingArrow_cat C) (Functor_cat
  WalkingArrow_cat C) (@kernel_adjunction_arrow_func C (@additive_preadditive C Prod t A) t
  (@additive_terminal_object C Prod t A) P) (@kernel_adjunction_family_boundary_diagram_func B C
  (@additive_preadditive C Prod t A) t (@additive_terminal_object C Prod t A) P U D h)))) (@eq_sym _ _ _
  (@one_cat_coimage_family_factor_path B C (@additive_preadditive C Prod t A) C1 t (@additive_terminal_object C
  Prod t A) T0 P Q (@kernel_adjunction_family_boundary_diagram_func B C (@additive_preadditive C Prod t A) t
  (@additive_terminal_object C Prod t A) P U D h)))) (@eq_trans _ _ _ _ (@eq_sym _ _ _ (@comp_assoc (Functor_cat B
  C) (@kernel_adjunction_family_func B C (@additive_preadditive C Prod t A) t (@additive_terminal_object C Prod t
  A) P (@transf_arrow_diagram_func B C (@fapp0 (Functor_cat B (Product_cat C C)) (Functor_cat B C)
  (@comp_cat_cov_func B (Product_cat C C) C Prod) (@Struct_sigma (Functor B C) (λ _ : τ (Functor B C), Functor B
  C) X U)) (@comp_cat_fapp0 B (Functor_cat WalkingArrow_cat C) C (@adjunction_coimage_func C
  (@additive_preadditive C Prod t A) t (@additive_terminal_object C Prod t A) T0 P Q)
  (@kernel_adjunction_family_boundary_diagram_func B C (@additive_preadditive C Prod t A) t
  (@additive_terminal_object C Prod t A) P U D h)) (@one_cat_difference_cospan_transf B C C1 Prod t A T0 X U
  (@comp_cat_fapp0 B (Functor_cat WalkingArrow_cat C) C (@adjunction_coimage_func C (@additive_preadditive C Prod
  t A) t (@additive_terminal_object C Prod t A) T0 P Q) (@kernel_adjunction_family_boundary_diagram_func B C
  (@additive_preadditive C Prod t A) t (@additive_terminal_object C Prod t A) P U D h))
  (@one_cat_boundary_coimage_lift B C C1 Prod t A T0 P Q N U D h X v z)
  (@cokernel_adjunction_family_projection_transf B C (@additive_preadditive C Prod t A) t T0 Q (@comp_cat_fapp0 B
  (Functor_cat WalkingArrow_cat C) (Functor_cat WalkingArrow_cat C) (@kernel_adjunction_arrow_func C
  (@additive_preadditive C Prod t A) t (@additive_terminal_object C Prod t A) P)
  (@kernel_adjunction_family_boundary_diagram_func B C (@additive_preadditive C Prod t A) t
  (@additive_terminal_object C Prod t A) P U D h)))))) U (@comp_cat_fapp0 B (Functor_cat WalkingArrow_cat C) C
  (@adjunction_coimage_func C (@additive_preadditive C Prod t A) t (@additive_terminal_object C Prod t A) T0 P Q)
  (@kernel_adjunction_family_boundary_diagram_func B C (@additive_preadditive C Prod t A) t
  (@additive_terminal_object C Prod t A) P U D h)) (@kernel_adjunction_family_func B C (@additive_preadditive C
  Prod t A) t (@additive_terminal_object C Prod t A) P D) (@fapp0 _ _ (@comp_cat_con_fapp1_func B (Functor_cat
  WalkingArrow_cat C) C (@kernel_adjunction_family_boundary_diagram_func B C (@additive_preadditive C Prod t A) t
  (@additive_terminal_object C Prod t A) P U D h) (@adjunction_coimage_func C (@additive_preadditive C Prod t A) t
  (@additive_terminal_object C Prod t A) T0 P Q) (@diagram_evaluation_at_func WalkingArrow_cat C
  walking_arrow_tgt)) (@one_cat_adjunction_coimage_to_target C (@additive_preadditive C Prod t A) C1 t
  (@additive_terminal_object C Prod t A) T0 P Q)) (@cokernel_adjunction_family_projection_transf B C
  (@additive_preadditive C Prod t A) t T0 Q (@comp_cat_fapp0 B (Functor_cat WalkingArrow_cat C) (Functor_cat
  WalkingArrow_cat C) (@kernel_adjunction_arrow_func C (@additive_preadditive C Prod t A) t
  (@additive_terminal_object C Prod t A) P) (@kernel_adjunction_family_boundary_diagram_func B C
  (@additive_preadditive C Prod t A) t (@additive_terminal_object C Prod t A) P U D h)))
  (@one_cat_boundary_representative_map B C C1 Prod t A T0 P Q N U D h X v z))) (@eq_trans _ _ _ _ (@eq_ap
  (@Transf B C (@kernel_adjunction_family_func B C (@additive_preadditive C Prod t A) t (@additive_terminal_object
  C Prod t A) P (@transf_arrow_diagram_func B C (@fapp0 (Functor_cat B (Product_cat C C)) (Functor_cat B C)
  (@comp_cat_cov_func B (Product_cat C C) C Prod) (@Struct_sigma (Functor B C) (λ _ : τ (Functor B C), Functor B
  C) X U)) (@comp_cat_fapp0 B (Functor_cat WalkingArrow_cat C) C (@adjunction_coimage_func C
  (@additive_preadditive C Prod t A) t (@additive_terminal_object C Prod t A) T0 P Q)
  (@kernel_adjunction_family_boundary_diagram_func B C (@additive_preadditive C Prod t A) t
  (@additive_terminal_object C Prod t A) P U D h)) (@one_cat_difference_cospan_transf B C C1 Prod t A T0 X U
  (@comp_cat_fapp0 B (Functor_cat WalkingArrow_cat C) C (@adjunction_coimage_func C (@additive_preadditive C Prod
  t A) t (@additive_terminal_object C Prod t A) T0 P Q) (@kernel_adjunction_family_boundary_diagram_func B C
  (@additive_preadditive C Prod t A) t (@additive_terminal_object C Prod t A) P U D h))
  (@one_cat_boundary_coimage_lift B C C1 Prod t A T0 P Q N U D h X v z)
  (@cokernel_adjunction_family_projection_transf B C (@additive_preadditive C Prod t A) t T0 Q (@comp_cat_fapp0 B
  (Functor_cat WalkingArrow_cat C) (Functor_cat WalkingArrow_cat C) (@kernel_adjunction_arrow_func C
  (@additive_preadditive C Prod t A) t (@additive_terminal_object C Prod t A) P)
  (@kernel_adjunction_family_boundary_diagram_func B C (@additive_preadditive C Prod t A) t
  (@additive_terminal_object C Prod t A) P U D h)))))) (@comp_cat_fapp0 B (Functor_cat WalkingArrow_cat C) C
  (@adjunction_coimage_func C (@additive_preadditive C Prod t A) t (@additive_terminal_object C Prod t A) T0 P Q)
  (@kernel_adjunction_family_boundary_diagram_func B C (@additive_preadditive C Prod t A) t
  (@additive_terminal_object C Prod t A) P U D h))) (@Transf B C (@kernel_adjunction_family_func B C
  (@additive_preadditive C Prod t A) t (@additive_terminal_object C Prod t A) P (@transf_arrow_diagram_func B C
  (@fapp0 (Functor_cat B (Product_cat C C)) (Functor_cat B C) (@comp_cat_cov_func B (Product_cat C C) C Prod)
  (@Struct_sigma (Functor B C) (λ _ : τ (Functor B C), Functor B C) X U)) (@comp_cat_fapp0 B (Functor_cat
  WalkingArrow_cat C) C (@adjunction_coimage_func C (@additive_preadditive C Prod t A) t
  (@additive_terminal_object C Prod t A) T0 P Q) (@kernel_adjunction_family_boundary_diagram_func B C
  (@additive_preadditive C Prod t A) t (@additive_terminal_object C Prod t A) P U D h))
  (@one_cat_difference_cospan_transf B C C1 Prod t A T0 X U (@comp_cat_fapp0 B (Functor_cat WalkingArrow_cat C) C
  (@adjunction_coimage_func C (@additive_preadditive C Prod t A) t (@additive_terminal_object C Prod t A) T0 P Q)
  (@kernel_adjunction_family_boundary_diagram_func B C (@additive_preadditive C Prod t A) t
  (@additive_terminal_object C Prod t A) P U D h)) (@one_cat_boundary_coimage_lift B C C1 Prod t A T0 P Q N
  U D h X v z) (@cokernel_adjunction_family_projection_transf B C (@additive_preadditive C Prod t A) t T0 Q
  (@comp_cat_fapp0 B (Functor_cat WalkingArrow_cat C) (Functor_cat WalkingArrow_cat C)
  (@kernel_adjunction_arrow_func C (@additive_preadditive C Prod t A) t (@additive_terminal_object C Prod t A) P)
  (@kernel_adjunction_family_boundary_diagram_func B C (@additive_preadditive C Prod t A) t
  (@additive_terminal_object C Prod t A) P U D h)))))) (@kernel_adjunction_family_func B C (@additive_preadditive
  C Prod t A) t (@additive_terminal_object C Prod t A) P D)) (λ j : τ (@Transf B C (@kernel_adjunction_family_func
  B C (@additive_preadditive C Prod t A) t (@additive_terminal_object C Prod t A) P (@transf_arrow_diagram_func B
  C (@fapp0 (Functor_cat B (Product_cat C C)) (Functor_cat B C) (@comp_cat_cov_func B (Product_cat C C) C Prod)
  (@Struct_sigma (Functor B C) (λ _ : τ (Functor B C), Functor B C) X U)) (@comp_cat_fapp0 B (Functor_cat
  WalkingArrow_cat C) C (@adjunction_coimage_func C (@additive_preadditive C Prod t A) t
  (@additive_terminal_object C Prod t A) T0 P Q) (@kernel_adjunction_family_boundary_diagram_func B C
  (@additive_preadditive C Prod t A) t (@additive_terminal_object C Prod t A) P U D h))
  (@one_cat_difference_cospan_transf B C C1 Prod t A T0 X U (@comp_cat_fapp0 B (Functor_cat WalkingArrow_cat C) C
  (@adjunction_coimage_func C (@additive_preadditive C Prod t A) t (@additive_terminal_object C Prod t A) T0 P Q)
  (@kernel_adjunction_family_boundary_diagram_func B C (@additive_preadditive C Prod t A) t
  (@additive_terminal_object C Prod t A) P U D h)) (@one_cat_boundary_coimage_lift B C C1 Prod t A T0 P Q N
  U D h X v z) (@cokernel_adjunction_family_projection_transf B C (@additive_preadditive C Prod t A) t T0 Q
  (@comp_cat_fapp0 B (Functor_cat WalkingArrow_cat C) (Functor_cat WalkingArrow_cat C)
  (@kernel_adjunction_arrow_func C (@additive_preadditive C Prod t A) t (@additive_terminal_object C Prod t A) P)
  (@kernel_adjunction_family_boundary_diagram_func B C (@additive_preadditive C Prod t A) t
  (@additive_terminal_object C Prod t A) P U D h)))))) (@comp_cat_fapp0 B (Functor_cat WalkingArrow_cat C) C
  (@adjunction_coimage_func C (@additive_preadditive C Prod t A) t (@additive_terminal_object C Prod t A) T0 P Q)
  (@kernel_adjunction_family_boundary_diagram_func B C (@additive_preadditive C Prod t A) t
  (@additive_terminal_object C Prod t A) P U D h))), (@comp_fapp0 (Functor_cat B C)
  (@kernel_adjunction_family_func B C (@additive_preadditive C Prod t A) t (@additive_terminal_object C Prod t A)
  P (@transf_arrow_diagram_func B C (@fapp0 (Functor_cat B (Product_cat C C)) (Functor_cat B C)
  (@comp_cat_cov_func B (Product_cat C C) C Prod) (@Struct_sigma (Functor B C) (λ _ : τ (Functor B C), Functor B
  C) X U)) (@comp_cat_fapp0 B (Functor_cat WalkingArrow_cat C) C (@adjunction_coimage_func C
  (@additive_preadditive C Prod t A) t (@additive_terminal_object C Prod t A) T0 P Q)
  (@kernel_adjunction_family_boundary_diagram_func B C (@additive_preadditive C Prod t A) t
  (@additive_terminal_object C Prod t A) P U D h)) (@one_cat_difference_cospan_transf B C C1 Prod t A T0 X U
  (@comp_cat_fapp0 B (Functor_cat WalkingArrow_cat C) C (@adjunction_coimage_func C (@additive_preadditive C Prod
  t A) t (@additive_terminal_object C Prod t A) T0 P Q) (@kernel_adjunction_family_boundary_diagram_func B C
  (@additive_preadditive C Prod t A) t (@additive_terminal_object C Prod t A) P U D h))
  (@one_cat_boundary_coimage_lift B C C1 Prod t A T0 P Q N U D h X v z)
  (@cokernel_adjunction_family_projection_transf B C (@additive_preadditive C Prod t A) t T0 Q (@comp_cat_fapp0 B
  (Functor_cat WalkingArrow_cat C) (Functor_cat WalkingArrow_cat C) (@kernel_adjunction_arrow_func C
  (@additive_preadditive C Prod t A) t (@additive_terminal_object C Prod t A) P)
  (@kernel_adjunction_family_boundary_diagram_func B C (@additive_preadditive C Prod t A) t
  (@additive_terminal_object C Prod t A) P U D h)))))) (@comp_cat_fapp0 B (Functor_cat WalkingArrow_cat C) C
  (@adjunction_coimage_func C (@additive_preadditive C Prod t A) t (@additive_terminal_object C Prod t A) T0 P Q)
  (@kernel_adjunction_family_boundary_diagram_func B C (@additive_preadditive C Prod t A) t
  (@additive_terminal_object C Prod t A) P U D h)) (@kernel_adjunction_family_func B C (@additive_preadditive C
  Prod t A) t (@additive_terminal_object C Prod t A) P D) (@fapp0 _ _ (@comp_cat_con_fapp1_func B (Functor_cat
  WalkingArrow_cat C) C (@kernel_adjunction_family_boundary_diagram_func B C (@additive_preadditive C Prod t A) t
  (@additive_terminal_object C Prod t A) P U D h) (@adjunction_coimage_func C (@additive_preadditive C Prod t A) t
  (@additive_terminal_object C Prod t A) T0 P Q) (@diagram_evaluation_at_func WalkingArrow_cat C
  walking_arrow_tgt)) (@one_cat_adjunction_coimage_to_target C (@additive_preadditive C Prod t A) C1 t
  (@additive_terminal_object C Prod t A) T0 P Q)) j)) (@comp_fapp0 (Functor_cat B C)
  (@kernel_adjunction_family_func B C (@additive_preadditive C Prod t A) t (@additive_terminal_object C Prod t A)
  P (@transf_arrow_diagram_func B C (@fapp0 (Functor_cat B (Product_cat C C)) (Functor_cat B C)
  (@comp_cat_cov_func B (Product_cat C C) C Prod) (@Struct_sigma (Functor B C) (λ _ : τ (Functor B C), Functor B
  C) X U)) (@comp_cat_fapp0 B (Functor_cat WalkingArrow_cat C) C (@adjunction_coimage_func C
  (@additive_preadditive C Prod t A) t (@additive_terminal_object C Prod t A) T0 P Q)
  (@kernel_adjunction_family_boundary_diagram_func B C (@additive_preadditive C Prod t A) t
  (@additive_terminal_object C Prod t A) P U D h)) (@one_cat_difference_cospan_transf B C C1 Prod t A T0 X U
  (@comp_cat_fapp0 B (Functor_cat WalkingArrow_cat C) C (@adjunction_coimage_func C (@additive_preadditive C Prod
  t A) t (@additive_terminal_object C Prod t A) T0 P Q) (@kernel_adjunction_family_boundary_diagram_func B C
  (@additive_preadditive C Prod t A) t (@additive_terminal_object C Prod t A) P U D h))
  (@one_cat_boundary_coimage_lift B C C1 Prod t A T0 P Q N U D h X v z)
  (@cokernel_adjunction_family_projection_transf B C (@additive_preadditive C Prod t A) t T0 Q (@comp_cat_fapp0 B
  (Functor_cat WalkingArrow_cat C) (Functor_cat WalkingArrow_cat C) (@kernel_adjunction_arrow_func C
  (@additive_preadditive C Prod t A) t (@additive_terminal_object C Prod t A) P)
  (@kernel_adjunction_family_boundary_diagram_func B C (@additive_preadditive C Prod t A) t
  (@additive_terminal_object C Prod t A) P U D h)))))) U (@comp_cat_fapp0 B (Functor_cat WalkingArrow_cat C) C
  (@adjunction_coimage_func C (@additive_preadditive C Prod t A) t (@additive_terminal_object C Prod t A) T0 P Q)
  (@kernel_adjunction_family_boundary_diagram_func B C (@additive_preadditive C Prod t A) t
  (@additive_terminal_object C Prod t A) P U D h)) (@cokernel_adjunction_family_projection_transf B C
  (@additive_preadditive C Prod t A) t T0 Q (@comp_cat_fapp0 B (Functor_cat WalkingArrow_cat C) (Functor_cat
  WalkingArrow_cat C) (@kernel_adjunction_arrow_func C (@additive_preadditive C Prod t A) t
  (@additive_terminal_object C Prod t A) P) (@kernel_adjunction_family_boundary_diagram_func B C
  (@additive_preadditive C Prod t A) t (@additive_terminal_object C Prod t A) P U D h)))
  (@one_cat_boundary_representative_map B C C1 Prod t A T0 P Q N U D h X v z)) (@comp_fapp0 (Functor_cat B
  C) (@kernel_adjunction_family_func B C (@additive_preadditive C Prod t A) t (@additive_terminal_object C Prod t
  A) P (@transf_arrow_diagram_func B C (@fapp0 (Functor_cat B (Product_cat C C)) (Functor_cat B C)
  (@comp_cat_cov_func B (Product_cat C C) C Prod) (@Struct_sigma (Functor B C) (λ _ : τ (Functor B C), Functor B
  C) X U)) (@comp_cat_fapp0 B (Functor_cat WalkingArrow_cat C) C (@adjunction_coimage_func C
  (@additive_preadditive C Prod t A) t (@additive_terminal_object C Prod t A) T0 P Q)
  (@kernel_adjunction_family_boundary_diagram_func B C (@additive_preadditive C Prod t A) t
  (@additive_terminal_object C Prod t A) P U D h)) (@one_cat_difference_cospan_transf B C C1 Prod t A T0 X U
  (@comp_cat_fapp0 B (Functor_cat WalkingArrow_cat C) C (@adjunction_coimage_func C (@additive_preadditive C Prod
  t A) t (@additive_terminal_object C Prod t A) T0 P Q) (@kernel_adjunction_family_boundary_diagram_func B C
  (@additive_preadditive C Prod t A) t (@additive_terminal_object C Prod t A) P U D h))
  (@one_cat_boundary_coimage_lift B C C1 Prod t A T0 P Q N U D h X v z)
  (@cokernel_adjunction_family_projection_transf B C (@additive_preadditive C Prod t A) t T0 Q (@comp_cat_fapp0 B
  (Functor_cat WalkingArrow_cat C) (Functor_cat WalkingArrow_cat C) (@kernel_adjunction_arrow_func C
  (@additive_preadditive C Prod t A) t (@additive_terminal_object C Prod t A) P)
  (@kernel_adjunction_family_boundary_diagram_func B C (@additive_preadditive C Prod t A) t
  (@additive_terminal_object C Prod t A) P U D h)))))) X (@comp_cat_fapp0 B (Functor_cat WalkingArrow_cat C) C
  (@adjunction_coimage_func C (@additive_preadditive C Prod t A) t (@additive_terminal_object C Prod t A) T0 P Q)
  (@kernel_adjunction_family_boundary_diagram_func B C (@additive_preadditive C Prod t A) t
  (@additive_terminal_object C Prod t A) P U D h)) (@one_cat_boundary_coimage_lift B C C1 Prod t A T0 P Q N
  U D h X v z) (@one_cat_boundary_representative_projection B C C1 Prod t A T0 P Q N U D h X v z)) (@eq_sym
  _ _ _ (@one_cat_cospan_kernel_compatibility B C C1 Prod t A T0 P Q X U (@comp_cat_fapp0 B (Functor_cat
  WalkingArrow_cat C) C (@adjunction_coimage_func C (@additive_preadditive C Prod t A) t
  (@additive_terminal_object C Prod t A) T0 P Q) (@kernel_adjunction_family_boundary_diagram_func B C
  (@additive_preadditive C Prod t A) t (@additive_terminal_object C Prod t A) P U D h))
  (@one_cat_boundary_coimage_lift B C C1 Prod t A T0 P Q N U D h X v z)
  (@cokernel_adjunction_family_projection_transf B C (@additive_preadditive C Prod t A) t T0 Q (@comp_cat_fapp0 B
  (Functor_cat WalkingArrow_cat C) (Functor_cat WalkingArrow_cat C) (@kernel_adjunction_arrow_func C
  (@additive_preadditive C Prod t A) t (@additive_terminal_object C Prod t A) P)
  (@kernel_adjunction_family_boundary_diagram_func B C (@additive_preadditive C Prod t A) t
  (@additive_terminal_object C Prod t A) P U D h)))))) (@eq_trans _ _ _ _ (@comp_assoc (Functor_cat B C)
  (@kernel_adjunction_family_func B C (@additive_preadditive C Prod t A) t (@additive_terminal_object C Prod t A)
  P (@transf_arrow_diagram_func B C (@fapp0 (Functor_cat B (Product_cat C C)) (Functor_cat B C)
  (@comp_cat_cov_func B (Product_cat C C) C Prod) (@Struct_sigma (Functor B C) (λ _ : τ (Functor B C), Functor B
  C) X U)) (@comp_cat_fapp0 B (Functor_cat WalkingArrow_cat C) C (@adjunction_coimage_func C
  (@additive_preadditive C Prod t A) t (@additive_terminal_object C Prod t A) T0 P Q)
  (@kernel_adjunction_family_boundary_diagram_func B C (@additive_preadditive C Prod t A) t
  (@additive_terminal_object C Prod t A) P U D h)) (@one_cat_difference_cospan_transf B C C1 Prod t A T0 X U
  (@comp_cat_fapp0 B (Functor_cat WalkingArrow_cat C) C (@adjunction_coimage_func C (@additive_preadditive C Prod
  t A) t (@additive_terminal_object C Prod t A) T0 P Q) (@kernel_adjunction_family_boundary_diagram_func B C
  (@additive_preadditive C Prod t A) t (@additive_terminal_object C Prod t A) P U D h))
  (@one_cat_boundary_coimage_lift B C C1 Prod t A T0 P Q N U D h X v z)
  (@cokernel_adjunction_family_projection_transf B C (@additive_preadditive C Prod t A) t T0 Q (@comp_cat_fapp0 B
  (Functor_cat WalkingArrow_cat C) (Functor_cat WalkingArrow_cat C) (@kernel_adjunction_arrow_func C
  (@additive_preadditive C Prod t A) t (@additive_terminal_object C Prod t A) P)
  (@kernel_adjunction_family_boundary_diagram_func B C (@additive_preadditive C Prod t A) t
  (@additive_terminal_object C Prod t A) P U D h)))))) X (@comp_cat_fapp0 B (Functor_cat WalkingArrow_cat C) C
  (@adjunction_coimage_func C (@additive_preadditive C Prod t A) t (@additive_terminal_object C Prod t A) T0 P Q)
  (@kernel_adjunction_family_boundary_diagram_func B C (@additive_preadditive C Prod t A) t
  (@additive_terminal_object C Prod t A) P U D h)) (@kernel_adjunction_family_func B C (@additive_preadditive C
  Prod t A) t (@additive_terminal_object C Prod t A) P D) (@fapp0 _ _ (@comp_cat_con_fapp1_func B (Functor_cat
  WalkingArrow_cat C) C (@kernel_adjunction_family_boundary_diagram_func B C (@additive_preadditive C Prod t A) t
  (@additive_terminal_object C Prod t A) P U D h) (@adjunction_coimage_func C (@additive_preadditive C Prod t A) t
  (@additive_terminal_object C Prod t A) T0 P Q) (@diagram_evaluation_at_func WalkingArrow_cat C
  walking_arrow_tgt)) (@one_cat_adjunction_coimage_to_target C (@additive_preadditive C Prod t A) C1 t
  (@additive_terminal_object C Prod t A) T0 P Q)) (@one_cat_boundary_coimage_lift B C C1 Prod t A T0 P Q N U
  D h X v z) (@one_cat_boundary_representative_projection B C C1 Prod t A T0 P Q N U D h X v z)) (@eq_ap
  (@Transf B C X (@kernel_adjunction_family_func B C (@additive_preadditive C Prod t A) t
  (@additive_terminal_object C Prod t A) P D)) (@Transf B C (@kernel_adjunction_family_func B C
  (@additive_preadditive C Prod t A) t (@additive_terminal_object C Prod t A) P (@transf_arrow_diagram_func B C
  (@fapp0 (Functor_cat B (Product_cat C C)) (Functor_cat B C) (@comp_cat_cov_func B (Product_cat C C) C Prod)
  (@Struct_sigma (Functor B C) (λ _ : τ (Functor B C), Functor B C) X U)) (@comp_cat_fapp0 B (Functor_cat
  WalkingArrow_cat C) C (@adjunction_coimage_func C (@additive_preadditive C Prod t A) t
  (@additive_terminal_object C Prod t A) T0 P Q) (@kernel_adjunction_family_boundary_diagram_func B C
  (@additive_preadditive C Prod t A) t (@additive_terminal_object C Prod t A) P U D h))
  (@one_cat_difference_cospan_transf B C C1 Prod t A T0 X U (@comp_cat_fapp0 B (Functor_cat WalkingArrow_cat C) C
  (@adjunction_coimage_func C (@additive_preadditive C Prod t A) t (@additive_terminal_object C Prod t A) T0 P Q)
  (@kernel_adjunction_family_boundary_diagram_func B C (@additive_preadditive C Prod t A) t
  (@additive_terminal_object C Prod t A) P U D h)) (@one_cat_boundary_coimage_lift B C C1 Prod t A T0 P Q N
  U D h X v z) (@cokernel_adjunction_family_projection_transf B C (@additive_preadditive C Prod t A) t T0 Q
  (@comp_cat_fapp0 B (Functor_cat WalkingArrow_cat C) (Functor_cat WalkingArrow_cat C)
  (@kernel_adjunction_arrow_func C (@additive_preadditive C Prod t A) t (@additive_terminal_object C Prod t A) P)
  (@kernel_adjunction_family_boundary_diagram_func B C (@additive_preadditive C Prod t A) t
  (@additive_terminal_object C Prod t A) P U D h)))))) (@kernel_adjunction_family_func B C (@additive_preadditive
  C Prod t A) t (@additive_terminal_object C Prod t A) P D)) (λ j : τ (@Transf B C X
  (@kernel_adjunction_family_func B C (@additive_preadditive C Prod t A) t (@additive_terminal_object C Prod t A)
  P D)), (@comp_fapp0 (Functor_cat B C) (@kernel_adjunction_family_func B C (@additive_preadditive C Prod t A) t
  (@additive_terminal_object C Prod t A) P (@transf_arrow_diagram_func B C (@fapp0 (Functor_cat B (Product_cat C
  C)) (Functor_cat B C) (@comp_cat_cov_func B (Product_cat C C) C Prod) (@Struct_sigma (Functor B C) (λ _ : τ
  (Functor B C), Functor B C) X U)) (@comp_cat_fapp0 B (Functor_cat WalkingArrow_cat C) C
  (@adjunction_coimage_func C (@additive_preadditive C Prod t A) t (@additive_terminal_object C Prod t A) T0 P Q)
  (@kernel_adjunction_family_boundary_diagram_func B C (@additive_preadditive C Prod t A) t
  (@additive_terminal_object C Prod t A) P U D h)) (@one_cat_difference_cospan_transf B C C1 Prod t A T0 X U
  (@comp_cat_fapp0 B (Functor_cat WalkingArrow_cat C) C (@adjunction_coimage_func C (@additive_preadditive C Prod
  t A) t (@additive_terminal_object C Prod t A) T0 P Q) (@kernel_adjunction_family_boundary_diagram_func B C
  (@additive_preadditive C Prod t A) t (@additive_terminal_object C Prod t A) P U D h))
  (@one_cat_boundary_coimage_lift B C C1 Prod t A T0 P Q N U D h X v z)
  (@cokernel_adjunction_family_projection_transf B C (@additive_preadditive C Prod t A) t T0 Q (@comp_cat_fapp0 B
  (Functor_cat WalkingArrow_cat C) (Functor_cat WalkingArrow_cat C) (@kernel_adjunction_arrow_func C
  (@additive_preadditive C Prod t A) t (@additive_terminal_object C Prod t A) P)
  (@kernel_adjunction_family_boundary_diagram_func B C (@additive_preadditive C Prod t A) t
  (@additive_terminal_object C Prod t A) P U D h)))))) X (@kernel_adjunction_family_func B C
  (@additive_preadditive C Prod t A) t (@additive_terminal_object C Prod t A) P D) j
  (@one_cat_boundary_representative_projection B C C1 Prod t A T0 P Q N U D h X v z))) (@comp_fapp0
  (Functor_cat B C) X (@comp_cat_fapp0 B (Functor_cat WalkingArrow_cat C) C (@adjunction_coimage_func C
  (@additive_preadditive C Prod t A) t (@additive_terminal_object C Prod t A) T0 P Q)
  (@kernel_adjunction_family_boundary_diagram_func B C (@additive_preadditive C Prod t A) t
  (@additive_terminal_object C Prod t A) P U D h)) (@kernel_adjunction_family_func B C (@additive_preadditive C
  Prod t A) t (@additive_terminal_object C Prod t A) P D) (@fapp0 _ _ (@comp_cat_con_fapp1_func B (Functor_cat
  WalkingArrow_cat C) C (@kernel_adjunction_family_boundary_diagram_func B C (@additive_preadditive C Prod t A) t
  (@additive_terminal_object C Prod t A) P U D h) (@adjunction_coimage_func C (@additive_preadditive C Prod t A) t
  (@additive_terminal_object C Prod t A) T0 P Q) (@diagram_evaluation_at_func WalkingArrow_cat C
  walking_arrow_tgt)) (@one_cat_adjunction_coimage_to_target C (@additive_preadditive C Prod t A) C1 t
  (@additive_terminal_object C Prod t A) T0 P Q)) (@one_cat_boundary_coimage_lift B C C1 Prod t A T0 P Q N U
  D h X v z)) v (@one_cat_boundary_coimage_lift_reconstruction B C C1 Prod t A T0 P Q N U D h X v z))))));

// The original quotient derives the boundary-representative cover without a supplied cover premise.
symbol one_cat_boundary_representative_cover [B C : Cat] (C1 : τ (IsNCat (cat_succ cat_zero) C)) [Prod : τ
  (Functor (Product_cat C C) C)] [t : τ (Obj C)] (A : τ (@AdditiveCategory C Prod t)) (T0 : τ (@TerminalObject
  (Op_cat C) t)) (P : τ (@KernelAdjunctionStructure C (@additive_preadditive C Prod t A) t
  (@additive_terminal_object C Prod t A))) (Q : τ (@CokernelAdjunctionStructure C (@additive_preadditive C Prod t
  A) t T0)) (N : τ (@OneCatAdjunctionNormality C (@additive_preadditive C Prod t A) C1 t
  (@additive_terminal_object C Prod t A) T0 P Q)) (U : τ (Functor B C)) (D : τ (Functor B (Functor_cat
  WalkingArrow_cat C))) (h : τ (@Transf B (Functor_cat WalkingArrow_cat C) (@comp_cat_fapp0 B C (Functor_cat
  WalkingArrow_cat C) (@terminal_arrow_diagram_func C t (@additive_terminal_object C Prod t A)) U) D)) (X : τ
  (Functor B C)) (v : τ (@Transf B C X (@kernel_adjunction_family_func B C (@additive_preadditive C Prod t A) t
  (@additive_terminal_object C Prod t A) P D))) (z : τ (@= (@Transf B C X (@homology_adjunction_family_func B C
  (@additive_preadditive C Prod t A) t (@additive_terminal_object C Prod t A) T0 P Q U D h)) (@comp_fapp0
  (Functor_cat B C) X (@kernel_adjunction_family_func B C (@additive_preadditive C Prod t A) t
  (@additive_terminal_object C Prod t A) P D) (@homology_adjunction_family_func B C (@additive_preadditive C Prod
  t A) t (@additive_terminal_object C Prod t A) T0 P Q U D h) (@homology_adjunction_family_projection_transf B C
  (@additive_preadditive C Prod t A) t (@additive_terminal_object C Prod t A) T0 P Q U D h) v)
  (@zero_arrow_family_zero_transf B C t (@additive_terminal_object C Prod t A) T0 X
  (@homology_adjunction_family_func B C (@additive_preadditive C Prod t A) t (@additive_terminal_object C Prod t
  A) T0 P Q U D h))))
 : τ (@OmegaEquivAlong (Functor_cat B C) (@comp_cat_fapp0 B (Functor_cat WalkingArrow_cat C) C
  (@adjunction_coimage_func C (@additive_preadditive C Prod t A) t (@additive_terminal_object C Prod t A) T0 P Q)
  (@transf_arrow_diagram_func B C (@kernel_adjunction_family_func B C (@additive_preadditive C Prod t A) t
  (@additive_terminal_object C Prod t A) P (@transf_arrow_diagram_func B C (@fapp0 (Functor_cat B (Product_cat C
  C)) (Functor_cat B C) (@comp_cat_cov_func B (Product_cat C C) C Prod) (@Struct_sigma (Functor B C) (λ _ : τ
  (Functor B C), Functor B C) X U)) (@comp_cat_fapp0 B (Functor_cat WalkingArrow_cat C) C
  (@adjunction_coimage_func C (@additive_preadditive C Prod t A) t (@additive_terminal_object C Prod t A) T0 P Q)
  (@kernel_adjunction_family_boundary_diagram_func B C (@additive_preadditive C Prod t A) t
  (@additive_terminal_object C Prod t A) P U D h)) (@one_cat_difference_cospan_transf B C C1 Prod t A T0 X U
  (@comp_cat_fapp0 B (Functor_cat WalkingArrow_cat C) C (@adjunction_coimage_func C (@additive_preadditive C Prod
  t A) t (@additive_terminal_object C Prod t A) T0 P Q) (@kernel_adjunction_family_boundary_diagram_func B C
  (@additive_preadditive C Prod t A) t (@additive_terminal_object C Prod t A) P U D h))
  (@one_cat_boundary_coimage_lift B C C1 Prod t A T0 P Q N U D h X v z)
  (@cokernel_adjunction_family_projection_transf B C (@additive_preadditive C Prod t A) t T0 Q (@comp_cat_fapp0 B
  (Functor_cat WalkingArrow_cat C) (Functor_cat WalkingArrow_cat C) (@kernel_adjunction_arrow_func C
  (@additive_preadditive C Prod t A) t (@additive_terminal_object C Prod t A) P)
  (@kernel_adjunction_family_boundary_diagram_func B C (@additive_preadditive C Prod t A) t
  (@additive_terminal_object C Prod t A) P U D h)))))) X (@one_cat_boundary_representative_projection B C C1
  Prod t A T0 P Q N U D h X v z))) X (@fapp0 _ _ (@comp_cat_con_fapp1_func B (Functor_cat WalkingArrow_cat C) C
  (@transf_arrow_diagram_func B C (@kernel_adjunction_family_func B C (@additive_preadditive C Prod t A) t
  (@additive_terminal_object C Prod t A) P (@transf_arrow_diagram_func B C (@fapp0 (Functor_cat B (Product_cat C
  C)) (Functor_cat B C) (@comp_cat_cov_func B (Product_cat C C) C Prod) (@Struct_sigma (Functor B C) (λ _ : τ
  (Functor B C), Functor B C) X U)) (@comp_cat_fapp0 B (Functor_cat WalkingArrow_cat C) C
  (@adjunction_coimage_func C (@additive_preadditive C Prod t A) t (@additive_terminal_object C Prod t A) T0 P Q)
  (@kernel_adjunction_family_boundary_diagram_func B C (@additive_preadditive C Prod t A) t
  (@additive_terminal_object C Prod t A) P U D h)) (@one_cat_difference_cospan_transf B C C1 Prod t A T0 X U
  (@comp_cat_fapp0 B (Functor_cat WalkingArrow_cat C) C (@adjunction_coimage_func C (@additive_preadditive C Prod
  t A) t (@additive_terminal_object C Prod t A) T0 P Q) (@kernel_adjunction_family_boundary_diagram_func B C
  (@additive_preadditive C Prod t A) t (@additive_terminal_object C Prod t A) P U D h))
  (@one_cat_boundary_coimage_lift B C C1 Prod t A T0 P Q N U D h X v z)
  (@cokernel_adjunction_family_projection_transf B C (@additive_preadditive C Prod t A) t T0 Q (@comp_cat_fapp0 B
  (Functor_cat WalkingArrow_cat C) (Functor_cat WalkingArrow_cat C) (@kernel_adjunction_arrow_func C
  (@additive_preadditive C Prod t A) t (@additive_terminal_object C Prod t A) P)
  (@kernel_adjunction_family_boundary_diagram_func B C (@additive_preadditive C Prod t A) t
  (@additive_terminal_object C Prod t A) P U D h)))))) X (@one_cat_boundary_representative_projection B C C1
  Prod t A T0 P Q N U D h X v z)) (@adjunction_coimage_func C (@additive_preadditive C Prod t A) t
  (@additive_terminal_object C Prod t A) T0 P Q) (@diagram_evaluation_at_func WalkingArrow_cat C
  walking_arrow_tgt)) (@one_cat_adjunction_coimage_to_target C (@additive_preadditive C Prod t A) C1 t
  (@additive_terminal_object C Prod t A) T0 P Q)))
≔ @one_cat_cospan_kernel_first_cover B C C1 Prod t A T0 P Q N X U (@comp_cat_fapp0 B (Functor_cat
  WalkingArrow_cat C) C (@adjunction_coimage_func C (@additive_preadditive C Prod t A) t
  (@additive_terminal_object C Prod t A) T0 P Q) (@kernel_adjunction_family_boundary_diagram_func B C
  (@additive_preadditive C Prod t A) t (@additive_terminal_object C Prod t A) P U D h))
  (@one_cat_boundary_coimage_lift B C C1 Prod t A T0 P Q N U D h X v z)
  (@cokernel_adjunction_family_projection_transf B C (@additive_preadditive C Prod t A) t T0 Q (@comp_cat_fapp0 B
  (Functor_cat WalkingArrow_cat C) (Functor_cat WalkingArrow_cat C) (@kernel_adjunction_arrow_func C
  (@additive_preadditive C Prod t A) t (@additive_terminal_object C Prod t A) P)
  (@kernel_adjunction_family_boundary_diagram_func B C (@additive_preadditive C Prod t A) t
  (@additive_terminal_object C Prod t A) P U D h))) (@one_cat_quotient_cokernel_zero B C
  (@additive_preadditive C Prod t A) C1 t (@additive_terminal_object C Prod t A) T0 Q (@comp_cat_fapp0 B
  (Functor_cat WalkingArrow_cat C) (Functor_cat WalkingArrow_cat C) (@kernel_adjunction_arrow_func C
  (@additive_preadditive C Prod t A) t (@additive_terminal_object C Prod t A) P)
  (@kernel_adjunction_family_boundary_diagram_func B C (@additive_preadditive C Prod t A) t
  (@additive_terminal_object C Prod t A) P U D h)));

// The same boundary-representative projection cancels whole maps.
symbol one_cat_boundary_representative_reflect_path [B C : Cat] (C1 : τ (IsNCat (cat_succ cat_zero) C))
  [Prod : τ (Functor (Product_cat C C) C)] [t : τ (Obj C)] (A : τ (@AdditiveCategory C Prod t)) (T0 : τ
  (@TerminalObject (Op_cat C) t)) (P : τ (@KernelAdjunctionStructure C (@additive_preadditive C Prod t A) t
  (@additive_terminal_object C Prod t A))) (Q : τ (@CokernelAdjunctionStructure C (@additive_preadditive C Prod t
  A) t T0)) (N : τ (@OneCatAdjunctionNormality C (@additive_preadditive C Prod t A) C1 t
  (@additive_terminal_object C Prod t A) T0 P Q)) (U : τ (Functor B C)) (D : τ (Functor B (Functor_cat
  WalkingArrow_cat C))) (h : τ (@Transf B (Functor_cat WalkingArrow_cat C) (@comp_cat_fapp0 B C (Functor_cat
  WalkingArrow_cat C) (@terminal_arrow_diagram_func C t (@additive_terminal_object C Prod t A)) U) D)) (X : τ
  (Functor B C)) (v : τ (@Transf B C X (@kernel_adjunction_family_func B C (@additive_preadditive C Prod t A) t
  (@additive_terminal_object C Prod t A) P D))) (z : τ (@= (@Transf B C X (@homology_adjunction_family_func B C
  (@additive_preadditive C Prod t A) t (@additive_terminal_object C Prod t A) T0 P Q U D h)) (@comp_fapp0
  (Functor_cat B C) X (@kernel_adjunction_family_func B C (@additive_preadditive C Prod t A) t
  (@additive_terminal_object C Prod t A) P D) (@homology_adjunction_family_func B C (@additive_preadditive C Prod
  t A) t (@additive_terminal_object C Prod t A) T0 P Q U D h) (@homology_adjunction_family_projection_transf B C
  (@additive_preadditive C Prod t A) t (@additive_terminal_object C Prod t A) T0 P Q U D h) v)
  (@zero_arrow_family_zero_transf B C t (@additive_terminal_object C Prod t A) T0 X
  (@homology_adjunction_family_func B C (@additive_preadditive C Prod t A) t (@additive_terminal_object C Prod t
  A) T0 P Q U D h)))) (Y : τ (Functor B C)) (a b : τ (@Transf B C X Y)) (e : τ (@= (@Transf B C
  (@kernel_adjunction_family_func B C (@additive_preadditive C Prod t A) t (@additive_terminal_object C Prod t A)
  P (@transf_arrow_diagram_func B C (@fapp0 (Functor_cat B (Product_cat C C)) (Functor_cat B C)
  (@comp_cat_cov_func B (Product_cat C C) C Prod) (@Struct_sigma (Functor B C) (λ _ : τ (Functor B C), Functor B
  C) X U)) (@comp_cat_fapp0 B (Functor_cat WalkingArrow_cat C) C (@adjunction_coimage_func C
  (@additive_preadditive C Prod t A) t (@additive_terminal_object C Prod t A) T0 P Q)
  (@kernel_adjunction_family_boundary_diagram_func B C (@additive_preadditive C Prod t A) t
  (@additive_terminal_object C Prod t A) P U D h)) (@one_cat_difference_cospan_transf B C C1 Prod t A T0 X U
  (@comp_cat_fapp0 B (Functor_cat WalkingArrow_cat C) C (@adjunction_coimage_func C (@additive_preadditive C Prod
  t A) t (@additive_terminal_object C Prod t A) T0 P Q) (@kernel_adjunction_family_boundary_diagram_func B C
  (@additive_preadditive C Prod t A) t (@additive_terminal_object C Prod t A) P U D h))
  (@one_cat_boundary_coimage_lift B C C1 Prod t A T0 P Q N U D h X v z)
  (@cokernel_adjunction_family_projection_transf B C (@additive_preadditive C Prod t A) t T0 Q (@comp_cat_fapp0 B
  (Functor_cat WalkingArrow_cat C) (Functor_cat WalkingArrow_cat C) (@kernel_adjunction_arrow_func C
  (@additive_preadditive C Prod t A) t (@additive_terminal_object C Prod t A) P)
  (@kernel_adjunction_family_boundary_diagram_func B C (@additive_preadditive C Prod t A) t
  (@additive_terminal_object C Prod t A) P U D h)))))) Y) (@comp_fapp0 (Functor_cat B C)
  (@kernel_adjunction_family_func B C (@additive_preadditive C Prod t A) t (@additive_terminal_object C Prod t A)
  P (@transf_arrow_diagram_func B C (@fapp0 (Functor_cat B (Product_cat C C)) (Functor_cat B C)
  (@comp_cat_cov_func B (Product_cat C C) C Prod) (@Struct_sigma (Functor B C) (λ _ : τ (Functor B C), Functor B
  C) X U)) (@comp_cat_fapp0 B (Functor_cat WalkingArrow_cat C) C (@adjunction_coimage_func C
  (@additive_preadditive C Prod t A) t (@additive_terminal_object C Prod t A) T0 P Q)
  (@kernel_adjunction_family_boundary_diagram_func B C (@additive_preadditive C Prod t A) t
  (@additive_terminal_object C Prod t A) P U D h)) (@one_cat_difference_cospan_transf B C C1 Prod t A T0 X U
  (@comp_cat_fapp0 B (Functor_cat WalkingArrow_cat C) C (@adjunction_coimage_func C (@additive_preadditive C Prod
  t A) t (@additive_terminal_object C Prod t A) T0 P Q) (@kernel_adjunction_family_boundary_diagram_func B C
  (@additive_preadditive C Prod t A) t (@additive_terminal_object C Prod t A) P U D h))
  (@one_cat_boundary_coimage_lift B C C1 Prod t A T0 P Q N U D h X v z)
  (@cokernel_adjunction_family_projection_transf B C (@additive_preadditive C Prod t A) t T0 Q (@comp_cat_fapp0 B
  (Functor_cat WalkingArrow_cat C) (Functor_cat WalkingArrow_cat C) (@kernel_adjunction_arrow_func C
  (@additive_preadditive C Prod t A) t (@additive_terminal_object C Prod t A) P)
  (@kernel_adjunction_family_boundary_diagram_func B C (@additive_preadditive C Prod t A) t
  (@additive_terminal_object C Prod t A) P U D h)))))) X Y a (@one_cat_boundary_representative_projection B
  C C1 Prod t A T0 P Q N U D h X v z)) (@comp_fapp0 (Functor_cat B C) (@kernel_adjunction_family_func B C
  (@additive_preadditive C Prod t A) t (@additive_terminal_object C Prod t A) P (@transf_arrow_diagram_func B C
  (@fapp0 (Functor_cat B (Product_cat C C)) (Functor_cat B C) (@comp_cat_cov_func B (Product_cat C C) C Prod)
  (@Struct_sigma (Functor B C) (λ _ : τ (Functor B C), Functor B C) X U)) (@comp_cat_fapp0 B (Functor_cat
  WalkingArrow_cat C) C (@adjunction_coimage_func C (@additive_preadditive C Prod t A) t
  (@additive_terminal_object C Prod t A) T0 P Q) (@kernel_adjunction_family_boundary_diagram_func B C
  (@additive_preadditive C Prod t A) t (@additive_terminal_object C Prod t A) P U D h))
  (@one_cat_difference_cospan_transf B C C1 Prod t A T0 X U (@comp_cat_fapp0 B (Functor_cat WalkingArrow_cat C) C
  (@adjunction_coimage_func C (@additive_preadditive C Prod t A) t (@additive_terminal_object C Prod t A) T0 P Q)
  (@kernel_adjunction_family_boundary_diagram_func B C (@additive_preadditive C Prod t A) t
  (@additive_terminal_object C Prod t A) P U D h)) (@one_cat_boundary_coimage_lift B C C1 Prod t A T0 P Q N
  U D h X v z) (@cokernel_adjunction_family_projection_transf B C (@additive_preadditive C Prod t A) t T0 Q
  (@comp_cat_fapp0 B (Functor_cat WalkingArrow_cat C) (Functor_cat WalkingArrow_cat C)
  (@kernel_adjunction_arrow_func C (@additive_preadditive C Prod t A) t (@additive_terminal_object C Prod t A) P)
  (@kernel_adjunction_family_boundary_diagram_func B C (@additive_preadditive C Prod t A) t
  (@additive_terminal_object C Prod t A) P U D h)))))) X Y b (@one_cat_boundary_representative_projection B
  C C1 Prod t A T0 P Q N U D h X v z))))
 : τ (@= (@Transf B C X Y) a b)
≔ @one_cat_cospan_kernel_first_reflect_path B C C1 Prod t A T0 P Q N X U (@comp_cat_fapp0 B (Functor_cat
  WalkingArrow_cat C) C (@adjunction_coimage_func C (@additive_preadditive C Prod t A) t
  (@additive_terminal_object C Prod t A) T0 P Q) (@kernel_adjunction_family_boundary_diagram_func B C
  (@additive_preadditive C Prod t A) t (@additive_terminal_object C Prod t A) P U D h))
  (@one_cat_boundary_coimage_lift B C C1 Prod t A T0 P Q N U D h X v z)
  (@cokernel_adjunction_family_projection_transf B C (@additive_preadditive C Prod t A) t T0 Q (@comp_cat_fapp0 B
  (Functor_cat WalkingArrow_cat C) (Functor_cat WalkingArrow_cat C) (@kernel_adjunction_arrow_func C
  (@additive_preadditive C Prod t A) t (@additive_terminal_object C Prod t A) P)
  (@kernel_adjunction_family_boundary_diagram_func B C (@additive_preadditive C Prod t A) t
  (@additive_terminal_object C Prod t A) P U D h))) (@one_cat_quotient_cokernel_zero B C
  (@additive_preadditive C Prod t A) C1 t (@additive_terminal_object C Prod t A) T0 Q (@comp_cat_fapp0 B
  (Functor_cat WalkingArrow_cat C) (Functor_cat WalkingArrow_cat C) (@kernel_adjunction_arrow_func C
  (@additive_preadditive C Prod t A) t (@additive_terminal_object C Prod t A) P)
  (@kernel_adjunction_family_boundary_diagram_func B C (@additive_preadditive C Prod t A) t
  (@additive_terminal_object C Prod t A) P U D h))) Y a b e;
