require open emdash.emdash3_2_one_cat_difference_cospans;
require open emdash.emdash3_2_one_cat_cokernel_family_annihilation;
require open emdash.emdash3_2_one_cat_short_exact_family_cancellation;

// The actual selected cokernel of the difference annihilates the original second leg.
symbol one_cat_difference_cospan_cokernel_second_zero [B C : Cat] (C1 : τ (IsNCat (cat_succ cat_zero) C))
  [Prod : τ (Functor (Product_cat C C) C)] [t : τ (Obj C)] (A : τ (@AdditiveCategory C Prod t)) (T0 : τ
  (@TerminalObject (Op_cat C) t)) (Q : τ (@CokernelAdjunctionStructure C (@additive_preadditive C Prod t A) t T0))
  (X Y Z : τ (Functor B C)) (f : τ (@Transf B C X Z)) (g : τ (@Transf B C Y Z))
 : τ (@= (@Transf B C Y (@comp_cat_fapp0 B (Functor_cat WalkingArrow_cat C) C (@cokernel_adjunction_func C
  (@additive_preadditive C Prod t A) t T0 Q) (@transf_arrow_diagram_func B C (@fapp0 (Functor_cat B (Product_cat C
  C)) (Functor_cat B C) (@comp_cat_cov_func B (Product_cat C C) C Prod) (@Struct_sigma (Functor B C) (λ _ : τ
  (Functor B C), Functor B C) X Y)) Z (@one_cat_difference_cospan_transf B C C1 Prod t A T0 X Y Z f g))))
  (@comp_fapp0 (Functor_cat B C) Y Z (@comp_cat_fapp0 B (Functor_cat WalkingArrow_cat C) C
  (@cokernel_adjunction_func C (@additive_preadditive C Prod t A) t T0 Q) (@transf_arrow_diagram_func B C (@fapp0
  (Functor_cat B (Product_cat C C)) (Functor_cat B C) (@comp_cat_cov_func B (Product_cat C C) C Prod)
  (@Struct_sigma (Functor B C) (λ _ : τ (Functor B C), Functor B C) X Y)) Z
  (@one_cat_difference_cospan_transf B C C1 Prod t A T0 X Y Z f g)))
  (@cokernel_adjunction_family_projection_transf B C (@additive_preadditive C Prod t A) t T0 Q
  (@transf_arrow_diagram_func B C (@fapp0 (Functor_cat B (Product_cat C C)) (Functor_cat B C) (@comp_cat_cov_func
  B (Product_cat C C) C Prod) (@Struct_sigma (Functor B C) (λ _ : τ (Functor B C), Functor B C) X Y)) Z
  (@one_cat_difference_cospan_transf B C C1 Prod t A T0 X Y Z f g))) g) (@zero_arrow_family_zero_transf B C
  t (@additive_terminal_object C Prod t A) T0 Y (@comp_cat_fapp0 B (Functor_cat WalkingArrow_cat C) C
  (@cokernel_adjunction_func C (@additive_preadditive C Prod t A) t T0 Q) (@transf_arrow_diagram_func B C (@fapp0
  (Functor_cat B (Product_cat C C)) (Functor_cat B C) (@comp_cat_cov_func B (Product_cat C C) C Prod)
  (@Struct_sigma (Functor B C) (λ _ : τ (Functor B C), Functor B C) X Y)) Z
  (@one_cat_difference_cospan_transf B C C1 Prod t A T0 X Y Z f g)))))
≔ @one_cat_difference_cospan_annihilator_path B C C1 Prod t A T0 X Y Z f g (@comp_cat_fapp0 B (Functor_cat
  WalkingArrow_cat C) C (@cokernel_adjunction_func C (@additive_preadditive C Prod t A) t T0 Q)
  (@transf_arrow_diagram_func B C (@fapp0 (Functor_cat B (Product_cat C C)) (Functor_cat B C) (@comp_cat_cov_func
  B (Product_cat C C) C Prod) (@Struct_sigma (Functor B C) (λ _ : τ (Functor B C), Functor B C) X Y)) Z
  (@one_cat_difference_cospan_transf B C C1 Prod t A T0 X Y Z f g)))
  (@cokernel_adjunction_family_projection_transf B C (@additive_preadditive C Prod t A) t T0 Q
  (@transf_arrow_diagram_func B C (@fapp0 (Functor_cat B (Product_cat C C)) (Functor_cat B C) (@comp_cat_cov_func
  B (Product_cat C C) C Prod) (@Struct_sigma (Functor B C) (λ _ : τ (Functor B C), Functor B C) X Y)) Z
  (@one_cat_difference_cospan_transf B C C1 Prod t A T0 X Y Z f g)))
  (@one_cat_cokernel_family_annihilation_path B C (@additive_preadditive C Prod t A) C1 t
  (@additive_terminal_object C Prod t A) T0 Q (@transf_arrow_diagram_func B C (@fapp0 (Functor_cat B (Product_cat
  C C)) (Functor_cat B C) (@comp_cat_cov_func B (Product_cat C C) C Prod) (@Struct_sigma (Functor B C) (λ _ : τ
  (Functor B C), Functor B C) X Y)) Z (@one_cat_difference_cospan_transf B C C1 Prod t A T0 X Y Z f g)));

// Original short-exact row cancellation forces this actual cokernel projection to zero.
symbol one_cat_difference_row_cokernel_zero [B C : Cat] (C1 : τ (IsNCat (cat_succ cat_zero) C)) [Prod : τ
  (Functor (Product_cat C C) C)] [t : τ (Obj C)] (A : τ (@AdditiveCategory C Prod t)) (T0 : τ (@TerminalObject
  (Op_cat C) t)) (P : τ (@KernelAdjunctionStructure C (@additive_preadditive C Prod t A) t
  (@additive_terminal_object C Prod t A))) (Q : τ (@CokernelAdjunctionStructure C (@additive_preadditive C Prod t
  A) t T0)) (U : τ (Functor B C)) (D : τ (Functor B (Functor_cat WalkingArrow_cat C))) (h : τ (@Transf B
  (Functor_cat WalkingArrow_cat C) (@comp_cat_fapp0 B C (Functor_cat WalkingArrow_cat C)
  (@terminal_arrow_diagram_func C t (@additive_terminal_object C Prod t A)) U) D)) (R : τ (@OneCatShortExactFamily
  B C (@additive_preadditive C Prod t A) C1 t (@additive_terminal_object C Prod t A) T0 P Q U D h)) (X : τ
  (Functor B C)) (f : τ (@Transf B C X (@diagram_family_at_func B WalkingArrow_cat C D walking_arrow_tgt)))
 : τ (@= (@Transf B C (@diagram_family_at_func B WalkingArrow_cat C D walking_arrow_tgt) (@comp_cat_fapp0 B
  (Functor_cat WalkingArrow_cat C) C (@cokernel_adjunction_func C (@additive_preadditive C Prod t A) t T0 Q)
  (@transf_arrow_diagram_func B C (@fapp0 (Functor_cat B (Product_cat C C)) (Functor_cat B C) (@comp_cat_cov_func
  B (Product_cat C C) C Prod) (@Struct_sigma (Functor B C) (λ _ : τ (Functor B C), Functor B C) X
  (@diagram_family_at_func B WalkingArrow_cat C D walking_arrow_src))) (@diagram_family_at_func B WalkingArrow_cat
  C D walking_arrow_tgt) (@one_cat_difference_cospan_transf B C C1 Prod t A T0 X (@diagram_family_at_func B
  WalkingArrow_cat C D walking_arrow_src) (@diagram_family_at_func B WalkingArrow_cat C D walking_arrow_tgt) f
  (@diagram_family_transf B WalkingArrow_cat C D walking_arrow_src walking_arrow_tgt walking_arrow_generator)))))
  (@cokernel_adjunction_family_projection_transf B C (@additive_preadditive C Prod t A) t T0 Q
  (@transf_arrow_diagram_func B C (@fapp0 (Functor_cat B (Product_cat C C)) (Functor_cat B C) (@comp_cat_cov_func
  B (Product_cat C C) C Prod) (@Struct_sigma (Functor B C) (λ _ : τ (Functor B C), Functor B C) X
  (@diagram_family_at_func B WalkingArrow_cat C D walking_arrow_src))) (@diagram_family_at_func B WalkingArrow_cat
  C D walking_arrow_tgt) (@one_cat_difference_cospan_transf B C C1 Prod t A T0 X (@diagram_family_at_func B
  WalkingArrow_cat C D walking_arrow_src) (@diagram_family_at_func B WalkingArrow_cat C D walking_arrow_tgt) f
  (@diagram_family_transf B WalkingArrow_cat C D walking_arrow_src walking_arrow_tgt walking_arrow_generator))))
  (@zero_arrow_family_zero_transf B C t (@additive_terminal_object C Prod t A) T0 (@diagram_family_at_func B
  WalkingArrow_cat C D walking_arrow_tgt) (@comp_cat_fapp0 B (Functor_cat WalkingArrow_cat C) C
  (@cokernel_adjunction_func C (@additive_preadditive C Prod t A) t T0 Q) (@transf_arrow_diagram_func B C (@fapp0
  (Functor_cat B (Product_cat C C)) (Functor_cat B C) (@comp_cat_cov_func B (Product_cat C C) C Prod)
  (@Struct_sigma (Functor B C) (λ _ : τ (Functor B C), Functor B C) X (@diagram_family_at_func B WalkingArrow_cat
  C D walking_arrow_src))) (@diagram_family_at_func B WalkingArrow_cat C D walking_arrow_tgt)
  (@one_cat_difference_cospan_transf B C C1 Prod t A T0 X (@diagram_family_at_func B WalkingArrow_cat C D
  walking_arrow_src) (@diagram_family_at_func B WalkingArrow_cat C D walking_arrow_tgt) f (@diagram_family_transf
  B WalkingArrow_cat C D walking_arrow_src walking_arrow_tgt walking_arrow_generator))))))
≔ @one_cat_short_exact_family_outgoing_reflect_path B C (@additive_preadditive C Prod t A) C1 t
  (@additive_terminal_object C Prod t A) T0 P Q U D h R (@comp_cat_fapp0 B (Functor_cat WalkingArrow_cat C) C
  (@cokernel_adjunction_func C (@additive_preadditive C Prod t A) t T0 Q) (@transf_arrow_diagram_func B C (@fapp0
  (Functor_cat B (Product_cat C C)) (Functor_cat B C) (@comp_cat_cov_func B (Product_cat C C) C Prod)
  (@Struct_sigma (Functor B C) (λ _ : τ (Functor B C), Functor B C) X (@diagram_family_at_func B WalkingArrow_cat
  C D walking_arrow_src))) (@diagram_family_at_func B WalkingArrow_cat C D walking_arrow_tgt)
  (@one_cat_difference_cospan_transf B C C1 Prod t A T0 X (@diagram_family_at_func B WalkingArrow_cat C D
  walking_arrow_src) (@diagram_family_at_func B WalkingArrow_cat C D walking_arrow_tgt) f (@diagram_family_transf
  B WalkingArrow_cat C D walking_arrow_src walking_arrow_tgt walking_arrow_generator))))
  (@cokernel_adjunction_family_projection_transf B C (@additive_preadditive C Prod t A) t T0 Q
  (@transf_arrow_diagram_func B C (@fapp0 (Functor_cat B (Product_cat C C)) (Functor_cat B C) (@comp_cat_cov_func
  B (Product_cat C C) C Prod) (@Struct_sigma (Functor B C) (λ _ : τ (Functor B C), Functor B C) X
  (@diagram_family_at_func B WalkingArrow_cat C D walking_arrow_src))) (@diagram_family_at_func B WalkingArrow_cat
  C D walking_arrow_tgt) (@one_cat_difference_cospan_transf B C C1 Prod t A T0 X (@diagram_family_at_func B
  WalkingArrow_cat C D walking_arrow_src) (@diagram_family_at_func B WalkingArrow_cat C D walking_arrow_tgt) f
  (@diagram_family_transf B WalkingArrow_cat C D walking_arrow_src walking_arrow_tgt walking_arrow_generator))))
  (@zero_arrow_family_zero_transf B C t (@additive_terminal_object C Prod t A) T0 (@diagram_family_at_func B
  WalkingArrow_cat C D walking_arrow_tgt) (@comp_cat_fapp0 B (Functor_cat WalkingArrow_cat C) C
  (@cokernel_adjunction_func C (@additive_preadditive C Prod t A) t T0 Q) (@transf_arrow_diagram_func B C (@fapp0
  (Functor_cat B (Product_cat C C)) (Functor_cat B C) (@comp_cat_cov_func B (Product_cat C C) C Prod)
  (@Struct_sigma (Functor B C) (λ _ : τ (Functor B C), Functor B C) X (@diagram_family_at_func B WalkingArrow_cat
  C D walking_arrow_src))) (@diagram_family_at_func B WalkingArrow_cat C D walking_arrow_tgt)
  (@one_cat_difference_cospan_transf B C C1 Prod t A T0 X (@diagram_family_at_func B WalkingArrow_cat C D
  walking_arrow_src) (@diagram_family_at_func B WalkingArrow_cat C D walking_arrow_tgt) f (@diagram_family_transf
  B WalkingArrow_cat C D walking_arrow_src walking_arrow_tgt walking_arrow_generator))))) (@eq_trans _ _ _ _
  (@one_cat_difference_cospan_cokernel_second_zero B C C1 Prod t A T0 Q X (@diagram_family_at_func B
  WalkingArrow_cat C D walking_arrow_src) (@diagram_family_at_func B WalkingArrow_cat C D walking_arrow_tgt) f
  (@diagram_family_transf B WalkingArrow_cat C D walking_arrow_src walking_arrow_tgt walking_arrow_generator))
  (@eq_sym _ _ _ (@one_cat_zero_family_precompose_path B C C1 t (@additive_terminal_object C Prod t A) T0
  (@diagram_family_at_func B WalkingArrow_cat C D walking_arrow_src) (@diagram_family_at_func B WalkingArrow_cat C
  D walking_arrow_tgt) (@comp_cat_fapp0 B (Functor_cat WalkingArrow_cat C) C (@cokernel_adjunction_func C
  (@additive_preadditive C Prod t A) t T0 Q) (@transf_arrow_diagram_func B C (@fapp0 (Functor_cat B (Product_cat C
  C)) (Functor_cat B C) (@comp_cat_cov_func B (Product_cat C C) C Prod) (@Struct_sigma (Functor B C) (λ _ : τ
  (Functor B C), Functor B C) X (@diagram_family_at_func B WalkingArrow_cat C D walking_arrow_src)))
  (@diagram_family_at_func B WalkingArrow_cat C D walking_arrow_tgt) (@one_cat_difference_cospan_transf B C
  C1 Prod t A T0 X (@diagram_family_at_func B WalkingArrow_cat C D walking_arrow_src) (@diagram_family_at_func B
  WalkingArrow_cat C D walking_arrow_tgt) f (@diagram_family_transf B WalkingArrow_cat C D walking_arrow_src
  walking_arrow_tgt walking_arrow_generator)))) (@diagram_family_transf B WalkingArrow_cat C D walking_arrow_src
  walking_arrow_tgt walking_arrow_generator))));
