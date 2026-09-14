require open emdash.emdash3_2_one_cat_coimage_cover_descent;
require open emdash.emdash3_2_one_cat_difference_cokernels;

// A zero actual cokernel of the second leg forces the difference cokernel to zero.
symbol one_cat_difference_cospan_zero_cokernel [B C : Cat] (C1 : τ (IsNCat (cat_succ cat_zero) C)) [Prod : τ
  (Functor (Product_cat C C) C)] [t : τ (Obj C)] (A : τ (@AdditiveCategory C Prod t)) (T0 : τ (@TerminalObject
  (Op_cat C) t)) (P : τ (@KernelAdjunctionStructure C (@additive_preadditive C Prod t A) t
  (@additive_terminal_object C Prod t A))) (Q : τ (@CokernelAdjunctionStructure C (@additive_preadditive C Prod t
  A) t T0)) (N : τ (@OneCatAdjunctionNormality C (@additive_preadditive C Prod t A) C1 t
  (@additive_terminal_object C Prod t A) T0 P Q)) (X Y Z : τ (Functor B C)) (f : τ (@Transf B C X Z)) (g : τ
  (@Transf B C Y Z)) (zg : τ (@= (@Transf B C Z (@comp_cat_fapp0 B (Functor_cat WalkingArrow_cat C) C
  (@cokernel_adjunction_func C (@additive_preadditive C Prod t A) t T0 Q) (@transf_arrow_diagram_func B C Y Z g)))
  (@cokernel_adjunction_family_projection_transf B C (@additive_preadditive C Prod t A) t T0 Q
  (@transf_arrow_diagram_func B C Y Z g)) (@zero_arrow_family_zero_transf B C t (@additive_terminal_object C Prod
  t A) T0 Z (@comp_cat_fapp0 B (Functor_cat WalkingArrow_cat C) C (@cokernel_adjunction_func C
  (@additive_preadditive C Prod t A) t T0 Q) (@transf_arrow_diagram_func B C Y Z g)))))
 : τ (@= (@Transf B C Z (@comp_cat_fapp0 B (Functor_cat WalkingArrow_cat C) C (@cokernel_adjunction_func C
  (@additive_preadditive C Prod t A) t T0 Q) (@transf_arrow_diagram_func B C (@fapp0 (Functor_cat B (Product_cat C
  C)) (Functor_cat B C) (@comp_cat_cov_func B (Product_cat C C) C Prod) (@Struct_sigma (Functor B C) (λ _ : τ
  (Functor B C), Functor B C) X Y)) Z (@one_cat_difference_cospan_transf B C C1 Prod t A T0 X Y Z f g))))
  (@cokernel_adjunction_family_projection_transf B C (@additive_preadditive C Prod t A) t T0 Q
  (@transf_arrow_diagram_func B C (@fapp0 (Functor_cat B (Product_cat C C)) (Functor_cat B C) (@comp_cat_cov_func
  B (Product_cat C C) C Prod) (@Struct_sigma (Functor B C) (λ _ : τ (Functor B C), Functor B C) X Y)) Z
  (@one_cat_difference_cospan_transf B C C1 Prod t A T0 X Y Z f g))) (@zero_arrow_family_zero_transf B C t
  (@additive_terminal_object C Prod t A) T0 Z (@comp_cat_fapp0 B (Functor_cat WalkingArrow_cat C) C
  (@cokernel_adjunction_func C (@additive_preadditive C Prod t A) t T0 Q) (@transf_arrow_diagram_func B C (@fapp0
  (Functor_cat B (Product_cat C C)) (Functor_cat B C) (@comp_cat_cov_func B (Product_cat C C) C Prod)
  (@Struct_sigma (Functor B C) (λ _ : τ (Functor B C), Functor B C) X Y)) Z (@one_cat_difference_cospan_transf B C
  C1 Prod t A T0 X Y Z f g)))))
≔ @one_cat_coimage_cover_reflect_path B C (@additive_preadditive C Prod t A) C1 t (@additive_terminal_object
  C Prod t A) T0 P Q (@transf_arrow_diagram_func B C Y Z g) (@one_cat_zero_cokernel_cover_omega B C
  (@additive_preadditive C Prod t A) C1 t (@additive_terminal_object C Prod t A) T0 P Q N
  (@transf_arrow_diagram_func B C Y Z g) zg) (@comp_cat_fapp0 B (Functor_cat WalkingArrow_cat C) C
  (@cokernel_adjunction_func C (@additive_preadditive C Prod t A) t T0 Q) (@transf_arrow_diagram_func B C (@fapp0
  (Functor_cat B (Product_cat C C)) (Functor_cat B C) (@comp_cat_cov_func B (Product_cat C C) C Prod)
  (@Struct_sigma (Functor B C) (λ _ : τ (Functor B C), Functor B C) X Y)) Z (@one_cat_difference_cospan_transf B C
  C1 Prod t A T0 X Y Z f g))) (@cokernel_adjunction_family_projection_transf B C (@additive_preadditive C Prod t
  A) t T0 Q (@transf_arrow_diagram_func B C (@fapp0 (Functor_cat B (Product_cat C C)) (Functor_cat B C)
  (@comp_cat_cov_func B (Product_cat C C) C Prod) (@Struct_sigma (Functor B C) (λ _ : τ (Functor B C), Functor B
  C) X Y)) Z (@one_cat_difference_cospan_transf B C C1 Prod t A T0 X Y Z f g))) (@zero_arrow_family_zero_transf B
  C t (@additive_terminal_object C Prod t A) T0 Z (@comp_cat_fapp0 B (Functor_cat WalkingArrow_cat C) C
  (@cokernel_adjunction_func C (@additive_preadditive C Prod t A) t T0 Q) (@transf_arrow_diagram_func B C (@fapp0
  (Functor_cat B (Product_cat C C)) (Functor_cat B C) (@comp_cat_cov_func B (Product_cat C C) C Prod)
  (@Struct_sigma (Functor B C) (λ _ : τ (Functor B C), Functor B C) X Y)) Z (@one_cat_difference_cospan_transf B C
  C1 Prod t A T0 X Y Z f g)))) (@eq_trans _ _ _ _ (@one_cat_difference_cospan_cokernel_second_zero B C C1 Prod t A
  T0 Q X Y Z f g) (@eq_sym _ _ _ (@one_cat_zero_family_precompose_path B C C1 t (@additive_terminal_object C Prod
  t A) T0 Y Z (@comp_cat_fapp0 B (Functor_cat WalkingArrow_cat C) C (@cokernel_adjunction_func C
  (@additive_preadditive C Prod t A) t T0 Q) (@transf_arrow_diagram_func B C (@fapp0 (Functor_cat B (Product_cat C
  C)) (Functor_cat B C) (@comp_cat_cov_func B (Product_cat C C) C Prod) (@Struct_sigma (Functor B C) (λ _ : τ
  (Functor B C), Functor B C) X Y)) Z (@one_cat_difference_cospan_transf B C C1 Prod t A T0 X Y Z f g))) g)));

// Derive the auxiliary cover through the same original coimage factor.
symbol one_cat_difference_cospan_zero_cokernel_cover [B C : Cat] (C1 : τ (IsNCat (cat_succ cat_zero) C))
  [Prod : τ (Functor (Product_cat C C) C)] [t : τ (Obj C)] (A : τ (@AdditiveCategory C Prod t)) (T0 : τ
  (@TerminalObject (Op_cat C) t)) (P : τ (@KernelAdjunctionStructure C (@additive_preadditive C Prod t A) t
  (@additive_terminal_object C Prod t A))) (Q : τ (@CokernelAdjunctionStructure C (@additive_preadditive C Prod t
  A) t T0)) (N : τ (@OneCatAdjunctionNormality C (@additive_preadditive C Prod t A) C1 t
  (@additive_terminal_object C Prod t A) T0 P Q)) (X Y Z : τ (Functor B C)) (f : τ (@Transf B C X Z)) (g : τ
  (@Transf B C Y Z)) (zg : τ (@= (@Transf B C Z (@comp_cat_fapp0 B (Functor_cat WalkingArrow_cat C) C
  (@cokernel_adjunction_func C (@additive_preadditive C Prod t A) t T0 Q) (@transf_arrow_diagram_func B C Y Z g)))
  (@cokernel_adjunction_family_projection_transf B C (@additive_preadditive C Prod t A) t T0 Q
  (@transf_arrow_diagram_func B C Y Z g)) (@zero_arrow_family_zero_transf B C t (@additive_terminal_object C Prod
  t A) T0 Z (@comp_cat_fapp0 B (Functor_cat WalkingArrow_cat C) C (@cokernel_adjunction_func C
  (@additive_preadditive C Prod t A) t T0 Q) (@transf_arrow_diagram_func B C Y Z g)))))
 : τ (@OmegaEquivAlong (Functor_cat B C) (@comp_cat_fapp0 B (Functor_cat WalkingArrow_cat C) C
  (@adjunction_coimage_func C (@additive_preadditive C Prod t A) t (@additive_terminal_object C Prod t A) T0 P Q)
  (@transf_arrow_diagram_func B C (@fapp0 (Functor_cat B (Product_cat C C)) (Functor_cat B C) (@comp_cat_cov_func
  B (Product_cat C C) C Prod) (@Struct_sigma (Functor B C) (λ _ : τ (Functor B C), Functor B C) X Y)) Z
  (@one_cat_difference_cospan_transf B C C1 Prod t A T0 X Y Z f g))) Z (@fapp0 _ _ (@comp_cat_con_fapp1_func B
  (Functor_cat WalkingArrow_cat C) C (@transf_arrow_diagram_func B C (@fapp0 (Functor_cat B (Product_cat C C))
  (Functor_cat B C) (@comp_cat_cov_func B (Product_cat C C) C Prod) (@Struct_sigma (Functor B C) (λ _ : τ (Functor
  B C), Functor B C) X Y)) Z (@one_cat_difference_cospan_transf B C C1 Prod t A T0 X Y Z f g))
  (@adjunction_coimage_func C (@additive_preadditive C Prod t A) t (@additive_terminal_object C Prod t A) T0 P Q)
  (@diagram_evaluation_at_func WalkingArrow_cat C walking_arrow_tgt)) (@one_cat_adjunction_coimage_to_target C
  (@additive_preadditive C Prod t A) C1 t (@additive_terminal_object C Prod t A) T0 P Q)))
≔ @one_cat_zero_cokernel_cover_omega B C (@additive_preadditive C Prod t A) C1 t (@additive_terminal_object C Prod
  t A) T0 P Q N (@transf_arrow_diagram_func B C (@fapp0 (Functor_cat B (Product_cat C C)) (Functor_cat B C)
  (@comp_cat_cov_func B (Product_cat C C) C Prod) (@Struct_sigma (Functor B C) (λ _ : τ (Functor B C), Functor B
  C) X Y)) Z (@one_cat_difference_cospan_transf B C C1 Prod t A T0 X Y Z f g))
  (@one_cat_difference_cospan_zero_cokernel B C C1 Prod t A T0 P Q N X Y Z f g zg);

// The original short-exact row derives the zero cokernel of its actual outgoing map.
symbol one_cat_short_exact_outgoing_cokernel_zero [B C : Cat] (C1 : τ (IsNCat (cat_succ cat_zero) C)) [Prod
  : τ (Functor (Product_cat C C) C)] [t : τ (Obj C)] (A : τ (@AdditiveCategory C Prod t)) (T0 : τ (@TerminalObject
  (Op_cat C) t)) (P : τ (@KernelAdjunctionStructure C (@additive_preadditive C Prod t A) t
  (@additive_terminal_object C Prod t A))) (Q : τ (@CokernelAdjunctionStructure C (@additive_preadditive C Prod t
  A) t T0)) (U : τ (Functor B C)) (D : τ (Functor B (Functor_cat WalkingArrow_cat C))) (h : τ (@Transf B
  (Functor_cat WalkingArrow_cat C) (@comp_cat_fapp0 B C (Functor_cat WalkingArrow_cat C)
  (@terminal_arrow_diagram_func C t (@additive_terminal_object C Prod t A)) U) D)) (R : τ (@OneCatShortExactFamily
  B C (@additive_preadditive C Prod t A) C1 t (@additive_terminal_object C Prod t A) T0 P Q U D h))
 : τ (@= (@Transf B C (@diagram_family_at_func B WalkingArrow_cat C D walking_arrow_tgt) (@comp_cat_fapp0 B
  (Functor_cat WalkingArrow_cat C) C (@cokernel_adjunction_func C (@additive_preadditive C Prod t A) t T0 Q)
  (@transf_arrow_diagram_func B C (@diagram_family_at_func B WalkingArrow_cat C D walking_arrow_src)
  (@diagram_family_at_func B WalkingArrow_cat C D walking_arrow_tgt) (@diagram_family_transf B WalkingArrow_cat C
  D walking_arrow_src walking_arrow_tgt walking_arrow_generator)))) (@cokernel_adjunction_family_projection_transf
  B C (@additive_preadditive C Prod t A) t T0 Q (@transf_arrow_diagram_func B C (@diagram_family_at_func B
  WalkingArrow_cat C D walking_arrow_src) (@diagram_family_at_func B WalkingArrow_cat C D walking_arrow_tgt)
  (@diagram_family_transf B WalkingArrow_cat C D walking_arrow_src walking_arrow_tgt walking_arrow_generator)))
  (@zero_arrow_family_zero_transf B C t (@additive_terminal_object C Prod t A) T0 (@diagram_family_at_func B
  WalkingArrow_cat C D walking_arrow_tgt) (@comp_cat_fapp0 B (Functor_cat WalkingArrow_cat C) C
  (@cokernel_adjunction_func C (@additive_preadditive C Prod t A) t T0 Q) (@transf_arrow_diagram_func B C
  (@diagram_family_at_func B WalkingArrow_cat C D walking_arrow_src) (@diagram_family_at_func B WalkingArrow_cat C
  D walking_arrow_tgt) (@diagram_family_transf B WalkingArrow_cat C D walking_arrow_src walking_arrow_tgt
  walking_arrow_generator)))))
≔ @one_cat_short_exact_family_outgoing_reflect_path B C (@additive_preadditive C Prod t A) C1 t
  (@additive_terminal_object C Prod t A) T0 P Q U D h R (@comp_cat_fapp0 B (Functor_cat WalkingArrow_cat C) C
  (@cokernel_adjunction_func C (@additive_preadditive C Prod t A) t T0 Q) (@transf_arrow_diagram_func B C
  (@diagram_family_at_func B WalkingArrow_cat C D walking_arrow_src) (@diagram_family_at_func B WalkingArrow_cat C
  D walking_arrow_tgt) (@diagram_family_transf B WalkingArrow_cat C D walking_arrow_src walking_arrow_tgt
  walking_arrow_generator))) (@cokernel_adjunction_family_projection_transf B C (@additive_preadditive C Prod t A)
  t T0 Q (@transf_arrow_diagram_func B C (@diagram_family_at_func B WalkingArrow_cat C D walking_arrow_src)
  (@diagram_family_at_func B WalkingArrow_cat C D walking_arrow_tgt) (@diagram_family_transf B WalkingArrow_cat C
  D walking_arrow_src walking_arrow_tgt walking_arrow_generator))) (@zero_arrow_family_zero_transf B C t
  (@additive_terminal_object C Prod t A) T0 (@diagram_family_at_func B WalkingArrow_cat C D walking_arrow_tgt)
  (@comp_cat_fapp0 B (Functor_cat WalkingArrow_cat C) C (@cokernel_adjunction_func C (@additive_preadditive C Prod
  t A) t T0 Q) (@transf_arrow_diagram_func B C (@diagram_family_at_func B WalkingArrow_cat C D walking_arrow_src)
  (@diagram_family_at_func B WalkingArrow_cat C D walking_arrow_tgt) (@diagram_family_transf B WalkingArrow_cat C
  D walking_arrow_src walking_arrow_tgt walking_arrow_generator)))) (@eq_trans _ _ _ _
  (@one_cat_cokernel_family_annihilation_path B C (@additive_preadditive C Prod t A) C1 t
  (@additive_terminal_object C Prod t A) T0 Q (@transf_arrow_diagram_func B C (@diagram_family_at_func B
  WalkingArrow_cat C D walking_arrow_src) (@diagram_family_at_func B WalkingArrow_cat C D walking_arrow_tgt)
  (@diagram_family_transf B WalkingArrow_cat C D walking_arrow_src walking_arrow_tgt walking_arrow_generator)))
  (@eq_sym _ _ _ (@one_cat_zero_family_precompose_path B C C1 t (@additive_terminal_object C Prod t A) T0
  (@diagram_family_at_func B WalkingArrow_cat C D walking_arrow_src) (@diagram_family_at_func B WalkingArrow_cat C
  D walking_arrow_tgt) (@comp_cat_fapp0 B (Functor_cat WalkingArrow_cat C) C (@cokernel_adjunction_func C
  (@additive_preadditive C Prod t A) t T0 Q) (@transf_arrow_diagram_func B C (@diagram_family_at_func B
  WalkingArrow_cat C D walking_arrow_src) (@diagram_family_at_func B WalkingArrow_cat C D walking_arrow_tgt)
  (@diagram_family_transf B WalkingArrow_cat C D walking_arrow_src walking_arrow_tgt walking_arrow_generator)))
  (@diagram_family_transf B WalkingArrow_cat C D walking_arrow_src walking_arrow_tgt walking_arrow_generator))));
