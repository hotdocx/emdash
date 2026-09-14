require open emdash.emdash3_2_one_cat_difference_covers;

// This actual row proves the cover, without an epicity or cover argument.
assert [B C : Cat] (C1 : τ (IsNCat (cat_succ cat_zero) C)) [Prod : τ (Functor (Product_cat C C) C)] [t : τ (Obj
  C)] (A : τ (@AdditiveCategory C Prod t)) (T0 : τ (@TerminalObject (Op_cat C) t)) (P : τ
  (@KernelAdjunctionStructure C (@additive_preadditive C Prod t A) t (@additive_terminal_object C Prod t A))) (Q :
  τ (@CokernelAdjunctionStructure C (@additive_preadditive C Prod t A) t T0)) (N : τ (@OneCatAdjunctionNormality C
  (@additive_preadditive C Prod t A) C1 t (@additive_terminal_object C Prod t A) T0 P Q)) (U : τ (Functor B C)) (D
  : τ (Functor B (Functor_cat WalkingArrow_cat C))) (h : τ (@Transf B (Functor_cat WalkingArrow_cat C)
  (@comp_cat_fapp0 B C (Functor_cat WalkingArrow_cat C) (@terminal_arrow_diagram_func C t
  (@additive_terminal_object C Prod t A)) U) D)) (R : τ (@OneCatShortExactFamily B C (@additive_preadditive C Prod
  t A) C1 t (@additive_terminal_object C Prod t A) T0 P Q U D h)) (X : τ (Functor B C)) (f : τ (@Transf B C X
  (@diagram_family_at_func B WalkingArrow_cat C D walking_arrow_tgt))) ⊢ @iso_evidence_to (Functor_cat B C)
  (@comp_cat_fapp0 B (Functor_cat WalkingArrow_cat C) C (@adjunction_coimage_func C (@additive_preadditive C Prod
  t A) t (@additive_terminal_object C Prod t A) T0 P Q) (@transf_arrow_diagram_func B C (@fapp0 (Functor_cat B
  (Product_cat C C)) (Functor_cat B C) (@comp_cat_cov_func B (Product_cat C C) C Prod) (@Struct_sigma (Functor B
  C) (λ _ : τ (Functor B C), Functor B C) X (@diagram_family_at_func B WalkingArrow_cat C D walking_arrow_src)))
  (@diagram_family_at_func B WalkingArrow_cat C D walking_arrow_tgt) (@one_cat_difference_cospan_transf B C C1
  Prod t A T0 X (@diagram_family_at_func B WalkingArrow_cat C D walking_arrow_src) (@diagram_family_at_func B
  WalkingArrow_cat C D walking_arrow_tgt) f (@diagram_family_transf B WalkingArrow_cat C D walking_arrow_src
  walking_arrow_tgt walking_arrow_generator)))) (@diagram_family_at_func B WalkingArrow_cat C D walking_arrow_tgt)
  (@omega_equiv_along_iso_evidence (Functor_cat B C) (@comp_cat_fapp0 B (Functor_cat WalkingArrow_cat C) C
  (@adjunction_coimage_func C (@additive_preadditive C Prod t A) t (@additive_terminal_object C Prod t A) T0 P Q)
  (@transf_arrow_diagram_func B C (@fapp0 (Functor_cat B (Product_cat C C)) (Functor_cat B C) (@comp_cat_cov_func
  B (Product_cat C C) C Prod) (@Struct_sigma (Functor B C) (λ _ : τ (Functor B C), Functor B C) X
  (@diagram_family_at_func B WalkingArrow_cat C D walking_arrow_src))) (@diagram_family_at_func B WalkingArrow_cat
  C D walking_arrow_tgt) (@one_cat_difference_cospan_transf B C C1 Prod t A T0 X (@diagram_family_at_func B
  WalkingArrow_cat C D walking_arrow_src) (@diagram_family_at_func B WalkingArrow_cat C D walking_arrow_tgt) f
  (@diagram_family_transf B WalkingArrow_cat C D walking_arrow_src walking_arrow_tgt walking_arrow_generator))))
  (@diagram_family_at_func B WalkingArrow_cat C D walking_arrow_tgt) (@fapp0 _ _ (@comp_cat_con_fapp1_func B
  (Functor_cat WalkingArrow_cat C) C (@transf_arrow_diagram_func B C (@fapp0 (Functor_cat B (Product_cat C C))
  (Functor_cat B C) (@comp_cat_cov_func B (Product_cat C C) C Prod) (@Struct_sigma (Functor B C) (λ _ : τ (Functor
  B C), Functor B C) X (@diagram_family_at_func B WalkingArrow_cat C D walking_arrow_src)))
  (@diagram_family_at_func B WalkingArrow_cat C D walking_arrow_tgt) (@one_cat_difference_cospan_transf B C C1
  Prod t A T0 X (@diagram_family_at_func B WalkingArrow_cat C D walking_arrow_src) (@diagram_family_at_func B
  WalkingArrow_cat C D walking_arrow_tgt) f (@diagram_family_transf B WalkingArrow_cat C D walking_arrow_src
  walking_arrow_tgt walking_arrow_generator))) (@adjunction_coimage_func C (@additive_preadditive C Prod t A) t
  (@additive_terminal_object C Prod t A) T0 P Q) (@diagram_evaluation_at_func WalkingArrow_cat C
  walking_arrow_tgt)) (@one_cat_adjunction_coimage_to_target C (@additive_preadditive C Prod t A) C1 t
  (@additive_terminal_object C Prod t A) T0 P Q)) (@one_cat_difference_row_cover_omega B C C1 Prod t A T0 P Q N U
  D h R X f)) ≡ (@fapp0 _ _ (@comp_cat_con_fapp1_func B (Functor_cat WalkingArrow_cat C) C
  (@transf_arrow_diagram_func B C (@fapp0 (Functor_cat B (Product_cat C C)) (Functor_cat B C) (@comp_cat_cov_func
  B (Product_cat C C) C Prod) (@Struct_sigma (Functor B C) (λ _ : τ (Functor B C), Functor B C) X
  (@diagram_family_at_func B WalkingArrow_cat C D walking_arrow_src))) (@diagram_family_at_func B WalkingArrow_cat
  C D walking_arrow_tgt) (@one_cat_difference_cospan_transf B C C1 Prod t A T0 X (@diagram_family_at_func B
  WalkingArrow_cat C D walking_arrow_src) (@diagram_family_at_func B WalkingArrow_cat C D walking_arrow_tgt) f
  (@diagram_family_transf B WalkingArrow_cat C D walking_arrow_src walking_arrow_tgt walking_arrow_generator)))
  (@adjunction_coimage_func C (@additive_preadditive C Prod t A) t (@additive_terminal_object C Prod t A) T0 P Q)
  (@diagram_evaluation_at_func WalkingArrow_cat C walking_arrow_tgt)) (@one_cat_adjunction_coimage_to_target C
  (@additive_preadditive C Prod t A) C1 t (@additive_terminal_object C Prod t A) T0 P Q));
assert [B C : Cat] (C1 : τ (IsNCat (cat_succ cat_zero) C)) [Prod : τ (Functor (Product_cat C C) C)] [t : τ (Obj
  C)] (A : τ (@AdditiveCategory C Prod t)) (T0 : τ (@TerminalObject (Op_cat C) t)) (P : τ
  (@KernelAdjunctionStructure C (@additive_preadditive C Prod t A) t (@additive_terminal_object C Prod t A))) (Q :
  τ (@CokernelAdjunctionStructure C (@additive_preadditive C Prod t A) t T0)) (N : τ (@OneCatAdjunctionNormality C
  (@additive_preadditive C Prod t A) C1 t (@additive_terminal_object C Prod t A) T0 P Q)) (U : τ (Functor B C)) (D
  : τ (Functor B (Functor_cat WalkingArrow_cat C))) (h : τ (@Transf B (Functor_cat WalkingArrow_cat C)
  (@comp_cat_fapp0 B C (Functor_cat WalkingArrow_cat C) (@terminal_arrow_diagram_func C t
  (@additive_terminal_object C Prod t A)) U) D)) (R : τ (@OneCatShortExactFamily B C (@additive_preadditive C Prod
  t A) C1 t (@additive_terminal_object C Prod t A) T0 P Q U D h)) (X : τ (Functor B C)) (f : τ (@Transf B C X
  (@diagram_family_at_func B WalkingArrow_cat C D walking_arrow_tgt))) ⊢ @omega_equiv_along_left_law (Functor_cat
  B C) (@comp_cat_fapp0 B (Functor_cat WalkingArrow_cat C) C (@adjunction_coimage_func C (@additive_preadditive C
  Prod t A) t (@additive_terminal_object C Prod t A) T0 P Q) (@transf_arrow_diagram_func B C (@fapp0 (Functor_cat
  B (Product_cat C C)) (Functor_cat B C) (@comp_cat_cov_func B (Product_cat C C) C Prod) (@Struct_sigma (Functor B
  C) (λ _ : τ (Functor B C), Functor B C) X (@diagram_family_at_func B WalkingArrow_cat C D walking_arrow_src)))
  (@diagram_family_at_func B WalkingArrow_cat C D walking_arrow_tgt) (@one_cat_difference_cospan_transf B C C1
  Prod t A T0 X (@diagram_family_at_func B WalkingArrow_cat C D walking_arrow_src) (@diagram_family_at_func B
  WalkingArrow_cat C D walking_arrow_tgt) f (@diagram_family_transf B WalkingArrow_cat C D walking_arrow_src
  walking_arrow_tgt walking_arrow_generator)))) (@diagram_family_at_func B WalkingArrow_cat C D walking_arrow_tgt)
  (@fapp0 _ _ (@comp_cat_con_fapp1_func B (Functor_cat WalkingArrow_cat C) C (@transf_arrow_diagram_func B C
  (@fapp0 (Functor_cat B (Product_cat C C)) (Functor_cat B C) (@comp_cat_cov_func B (Product_cat C C) C Prod)
  (@Struct_sigma (Functor B C) (λ _ : τ (Functor B C), Functor B C) X (@diagram_family_at_func B WalkingArrow_cat
  C D walking_arrow_src))) (@diagram_family_at_func B WalkingArrow_cat C D walking_arrow_tgt)
  (@one_cat_difference_cospan_transf B C C1 Prod t A T0 X (@diagram_family_at_func B WalkingArrow_cat C D
  walking_arrow_src) (@diagram_family_at_func B WalkingArrow_cat C D walking_arrow_tgt) f (@diagram_family_transf
  B WalkingArrow_cat C D walking_arrow_src walking_arrow_tgt walking_arrow_generator))) (@adjunction_coimage_func
  C (@additive_preadditive C Prod t A) t (@additive_terminal_object C Prod t A) T0 P Q)
  (@diagram_evaluation_at_func WalkingArrow_cat C walking_arrow_tgt)) (@one_cat_adjunction_coimage_to_target C
  (@additive_preadditive C Prod t A) C1 t (@additive_terminal_object C Prod t A) T0 P Q))
  (@one_cat_difference_row_cover_omega B C C1 Prod t A T0 P Q N U D h R X f) : τ (@= (@Transf B C (@comp_cat_fapp0
  B (Functor_cat WalkingArrow_cat C) C (@adjunction_coimage_func C (@additive_preadditive C Prod t A) t
  (@additive_terminal_object C Prod t A) T0 P Q) (@transf_arrow_diagram_func B C (@fapp0 (Functor_cat B
  (Product_cat C C)) (Functor_cat B C) (@comp_cat_cov_func B (Product_cat C C) C Prod) (@Struct_sigma (Functor B
  C) (λ _ : τ (Functor B C), Functor B C) X (@diagram_family_at_func B WalkingArrow_cat C D walking_arrow_src)))
  (@diagram_family_at_func B WalkingArrow_cat C D walking_arrow_tgt) (@one_cat_difference_cospan_transf B C C1
  Prod t A T0 X (@diagram_family_at_func B WalkingArrow_cat C D walking_arrow_src) (@diagram_family_at_func B
  WalkingArrow_cat C D walking_arrow_tgt) f (@diagram_family_transf B WalkingArrow_cat C D walking_arrow_src
  walking_arrow_tgt walking_arrow_generator)))) (@comp_cat_fapp0 B (Functor_cat WalkingArrow_cat C) C
  (@adjunction_coimage_func C (@additive_preadditive C Prod t A) t (@additive_terminal_object C Prod t A) T0 P Q)
  (@transf_arrow_diagram_func B C (@fapp0 (Functor_cat B (Product_cat C C)) (Functor_cat B C) (@comp_cat_cov_func
  B (Product_cat C C) C Prod) (@Struct_sigma (Functor B C) (λ _ : τ (Functor B C), Functor B C) X
  (@diagram_family_at_func B WalkingArrow_cat C D walking_arrow_src))) (@diagram_family_at_func B WalkingArrow_cat
  C D walking_arrow_tgt) (@one_cat_difference_cospan_transf B C C1 Prod t A T0 X (@diagram_family_at_func B
  WalkingArrow_cat C D walking_arrow_src) (@diagram_family_at_func B WalkingArrow_cat C D walking_arrow_tgt) f
  (@diagram_family_transf B WalkingArrow_cat C D walking_arrow_src walking_arrow_tgt walking_arrow_generator)))))
  (@comp_fapp0 (Functor_cat B C) (@comp_cat_fapp0 B (Functor_cat WalkingArrow_cat C) C (@adjunction_coimage_func C
  (@additive_preadditive C Prod t A) t (@additive_terminal_object C Prod t A) T0 P Q) (@transf_arrow_diagram_func
  B C (@fapp0 (Functor_cat B (Product_cat C C)) (Functor_cat B C) (@comp_cat_cov_func B (Product_cat C C) C Prod)
  (@Struct_sigma (Functor B C) (λ _ : τ (Functor B C), Functor B C) X (@diagram_family_at_func B WalkingArrow_cat
  C D walking_arrow_src))) (@diagram_family_at_func B WalkingArrow_cat C D walking_arrow_tgt)
  (@one_cat_difference_cospan_transf B C C1 Prod t A T0 X (@diagram_family_at_func B WalkingArrow_cat C D
  walking_arrow_src) (@diagram_family_at_func B WalkingArrow_cat C D walking_arrow_tgt) f (@diagram_family_transf
  B WalkingArrow_cat C D walking_arrow_src walking_arrow_tgt walking_arrow_generator)))) (@diagram_family_at_func
  B WalkingArrow_cat C D walking_arrow_tgt) (@comp_cat_fapp0 B (Functor_cat WalkingArrow_cat C) C
  (@adjunction_coimage_func C (@additive_preadditive C Prod t A) t (@additive_terminal_object C Prod t A) T0 P Q)
  (@transf_arrow_diagram_func B C (@fapp0 (Functor_cat B (Product_cat C C)) (Functor_cat B C) (@comp_cat_cov_func
  B (Product_cat C C) C Prod) (@Struct_sigma (Functor B C) (λ _ : τ (Functor B C), Functor B C) X
  (@diagram_family_at_func B WalkingArrow_cat C D walking_arrow_src))) (@diagram_family_at_func B WalkingArrow_cat
  C D walking_arrow_tgt) (@one_cat_difference_cospan_transf B C C1 Prod t A T0 X (@diagram_family_at_func B
  WalkingArrow_cat C D walking_arrow_src) (@diagram_family_at_func B WalkingArrow_cat C D walking_arrow_tgt) f
  (@diagram_family_transf B WalkingArrow_cat C D walking_arrow_src walking_arrow_tgt walking_arrow_generator))))
  (@omega_equiv_along_left_inv (Functor_cat B C) (@comp_cat_fapp0 B (Functor_cat WalkingArrow_cat C) C
  (@adjunction_coimage_func C (@additive_preadditive C Prod t A) t (@additive_terminal_object C Prod t A) T0 P Q)
  (@transf_arrow_diagram_func B C (@fapp0 (Functor_cat B (Product_cat C C)) (Functor_cat B C) (@comp_cat_cov_func
  B (Product_cat C C) C Prod) (@Struct_sigma (Functor B C) (λ _ : τ (Functor B C), Functor B C) X
  (@diagram_family_at_func B WalkingArrow_cat C D walking_arrow_src))) (@diagram_family_at_func B WalkingArrow_cat
  C D walking_arrow_tgt) (@one_cat_difference_cospan_transf B C C1 Prod t A T0 X (@diagram_family_at_func B
  WalkingArrow_cat C D walking_arrow_src) (@diagram_family_at_func B WalkingArrow_cat C D walking_arrow_tgt) f
  (@diagram_family_transf B WalkingArrow_cat C D walking_arrow_src walking_arrow_tgt walking_arrow_generator))))
  (@diagram_family_at_func B WalkingArrow_cat C D walking_arrow_tgt) (@fapp0 _ _ (@comp_cat_con_fapp1_func B
  (Functor_cat WalkingArrow_cat C) C (@transf_arrow_diagram_func B C (@fapp0 (Functor_cat B (Product_cat C C))
  (Functor_cat B C) (@comp_cat_cov_func B (Product_cat C C) C Prod) (@Struct_sigma (Functor B C) (λ _ : τ (Functor
  B C), Functor B C) X (@diagram_family_at_func B WalkingArrow_cat C D walking_arrow_src)))
  (@diagram_family_at_func B WalkingArrow_cat C D walking_arrow_tgt) (@one_cat_difference_cospan_transf B C C1
  Prod t A T0 X (@diagram_family_at_func B WalkingArrow_cat C D walking_arrow_src) (@diagram_family_at_func B
  WalkingArrow_cat C D walking_arrow_tgt) f (@diagram_family_transf B WalkingArrow_cat C D walking_arrow_src
  walking_arrow_tgt walking_arrow_generator))) (@adjunction_coimage_func C (@additive_preadditive C Prod t A) t
  (@additive_terminal_object C Prod t A) T0 P Q) (@diagram_evaluation_at_func WalkingArrow_cat C
  walking_arrow_tgt)) (@one_cat_adjunction_coimage_to_target C (@additive_preadditive C Prod t A) C1 t
  (@additive_terminal_object C Prod t A) T0 P Q)) (@one_cat_difference_row_cover_omega B C C1 Prod t A T0 P Q N U
  D h R X f)) (@fapp0 _ _ (@comp_cat_con_fapp1_func B (Functor_cat WalkingArrow_cat C) C
  (@transf_arrow_diagram_func B C (@fapp0 (Functor_cat B (Product_cat C C)) (Functor_cat B C) (@comp_cat_cov_func
  B (Product_cat C C) C Prod) (@Struct_sigma (Functor B C) (λ _ : τ (Functor B C), Functor B C) X
  (@diagram_family_at_func B WalkingArrow_cat C D walking_arrow_src))) (@diagram_family_at_func B WalkingArrow_cat
  C D walking_arrow_tgt) (@one_cat_difference_cospan_transf B C C1 Prod t A T0 X (@diagram_family_at_func B
  WalkingArrow_cat C D walking_arrow_src) (@diagram_family_at_func B WalkingArrow_cat C D walking_arrow_tgt) f
  (@diagram_family_transf B WalkingArrow_cat C D walking_arrow_src walking_arrow_tgt walking_arrow_generator)))
  (@adjunction_coimage_func C (@additive_preadditive C Prod t A) t (@additive_terminal_object C Prod t A) T0 P Q)
  (@diagram_evaluation_at_func WalkingArrow_cat C walking_arrow_tgt)) (@one_cat_adjunction_coimage_to_target C
  (@additive_preadditive C Prod t A) C1 t (@additive_terminal_object C Prod t A) T0 P Q))) (@id (Functor_cat B C)
  (@comp_cat_fapp0 B (Functor_cat WalkingArrow_cat C) C (@adjunction_coimage_func C (@additive_preadditive C Prod
  t A) t (@additive_terminal_object C Prod t A) T0 P Q) (@transf_arrow_diagram_func B C (@fapp0 (Functor_cat B
  (Product_cat C C)) (Functor_cat B C) (@comp_cat_cov_func B (Product_cat C C) C Prod) (@Struct_sigma (Functor B
  C) (λ _ : τ (Functor B C), Functor B C) X (@diagram_family_at_func B WalkingArrow_cat C D walking_arrow_src)))
  (@diagram_family_at_func B WalkingArrow_cat C D walking_arrow_tgt) (@one_cat_difference_cospan_transf B C C1
  Prod t A T0 X (@diagram_family_at_func B WalkingArrow_cat C D walking_arrow_src) (@diagram_family_at_func B
  WalkingArrow_cat C D walking_arrow_tgt) f (@diagram_family_transf B WalkingArrow_cat C D walking_arrow_src
  walking_arrow_tgt walking_arrow_generator))))));
assert [B C : Cat] (C1 : τ (IsNCat (cat_succ cat_zero) C)) [Prod : τ (Functor (Product_cat C C) C)] [t : τ (Obj
  C)] (A : τ (@AdditiveCategory C Prod t)) (T0 : τ (@TerminalObject (Op_cat C) t)) (P : τ
  (@KernelAdjunctionStructure C (@additive_preadditive C Prod t A) t (@additive_terminal_object C Prod t A))) (Q :
  τ (@CokernelAdjunctionStructure C (@additive_preadditive C Prod t A) t T0)) (N : τ (@OneCatAdjunctionNormality C
  (@additive_preadditive C Prod t A) C1 t (@additive_terminal_object C Prod t A) T0 P Q)) (U : τ (Functor B C)) (D
  : τ (Functor B (Functor_cat WalkingArrow_cat C))) (h : τ (@Transf B (Functor_cat WalkingArrow_cat C)
  (@comp_cat_fapp0 B C (Functor_cat WalkingArrow_cat C) (@terminal_arrow_diagram_func C t
  (@additive_terminal_object C Prod t A)) U) D)) (R : τ (@OneCatShortExactFamily B C (@additive_preadditive C Prod
  t A) C1 t (@additive_terminal_object C Prod t A) T0 P Q U D h)) (X : τ (Functor B C)) (f : τ (@Transf B C X
  (@diagram_family_at_func B WalkingArrow_cat C D walking_arrow_tgt))) ⊢ @omega_equiv_left_as_right_law
  (Functor_cat B C) (@comp_cat_fapp0 B (Functor_cat WalkingArrow_cat C) C (@adjunction_coimage_func C
  (@additive_preadditive C Prod t A) t (@additive_terminal_object C Prod t A) T0 P Q) (@transf_arrow_diagram_func
  B C (@fapp0 (Functor_cat B (Product_cat C C)) (Functor_cat B C) (@comp_cat_cov_func B (Product_cat C C) C Prod)
  (@Struct_sigma (Functor B C) (λ _ : τ (Functor B C), Functor B C) X (@diagram_family_at_func B WalkingArrow_cat
  C D walking_arrow_src))) (@diagram_family_at_func B WalkingArrow_cat C D walking_arrow_tgt)
  (@one_cat_difference_cospan_transf B C C1 Prod t A T0 X (@diagram_family_at_func B WalkingArrow_cat C D
  walking_arrow_src) (@diagram_family_at_func B WalkingArrow_cat C D walking_arrow_tgt) f (@diagram_family_transf
  B WalkingArrow_cat C D walking_arrow_src walking_arrow_tgt walking_arrow_generator)))) (@diagram_family_at_func
  B WalkingArrow_cat C D walking_arrow_tgt) (@fapp0 _ _ (@comp_cat_con_fapp1_func B (Functor_cat WalkingArrow_cat
  C) C (@transf_arrow_diagram_func B C (@fapp0 (Functor_cat B (Product_cat C C)) (Functor_cat B C)
  (@comp_cat_cov_func B (Product_cat C C) C Prod) (@Struct_sigma (Functor B C) (λ _ : τ (Functor B C), Functor B
  C) X (@diagram_family_at_func B WalkingArrow_cat C D walking_arrow_src))) (@diagram_family_at_func B
  WalkingArrow_cat C D walking_arrow_tgt) (@one_cat_difference_cospan_transf B C C1 Prod t A T0 X
  (@diagram_family_at_func B WalkingArrow_cat C D walking_arrow_src) (@diagram_family_at_func B WalkingArrow_cat C
  D walking_arrow_tgt) f (@diagram_family_transf B WalkingArrow_cat C D walking_arrow_src walking_arrow_tgt
  walking_arrow_generator))) (@adjunction_coimage_func C (@additive_preadditive C Prod t A) t
  (@additive_terminal_object C Prod t A) T0 P Q) (@diagram_evaluation_at_func WalkingArrow_cat C
  walking_arrow_tgt)) (@one_cat_adjunction_coimage_to_target C (@additive_preadditive C Prod t A) C1 t
  (@additive_terminal_object C Prod t A) T0 P Q)) (@one_cat_difference_row_cover_omega B C C1 Prod t A T0 P Q N U
  D h R X f) : τ (@= (@Transf B C (@diagram_family_at_func B WalkingArrow_cat C D walking_arrow_tgt)
  (@diagram_family_at_func B WalkingArrow_cat C D walking_arrow_tgt)) (@comp_fapp0 (Functor_cat B C)
  (@diagram_family_at_func B WalkingArrow_cat C D walking_arrow_tgt) (@comp_cat_fapp0 B (Functor_cat
  WalkingArrow_cat C) C (@adjunction_coimage_func C (@additive_preadditive C Prod t A) t
  (@additive_terminal_object C Prod t A) T0 P Q) (@transf_arrow_diagram_func B C (@fapp0 (Functor_cat B
  (Product_cat C C)) (Functor_cat B C) (@comp_cat_cov_func B (Product_cat C C) C Prod) (@Struct_sigma (Functor B
  C) (λ _ : τ (Functor B C), Functor B C) X (@diagram_family_at_func B WalkingArrow_cat C D walking_arrow_src)))
  (@diagram_family_at_func B WalkingArrow_cat C D walking_arrow_tgt) (@one_cat_difference_cospan_transf B C C1
  Prod t A T0 X (@diagram_family_at_func B WalkingArrow_cat C D walking_arrow_src) (@diagram_family_at_func B
  WalkingArrow_cat C D walking_arrow_tgt) f (@diagram_family_transf B WalkingArrow_cat C D walking_arrow_src
  walking_arrow_tgt walking_arrow_generator)))) (@diagram_family_at_func B WalkingArrow_cat C D walking_arrow_tgt)
  (@fapp0 _ _ (@comp_cat_con_fapp1_func B (Functor_cat WalkingArrow_cat C) C (@transf_arrow_diagram_func B C
  (@fapp0 (Functor_cat B (Product_cat C C)) (Functor_cat B C) (@comp_cat_cov_func B (Product_cat C C) C Prod)
  (@Struct_sigma (Functor B C) (λ _ : τ (Functor B C), Functor B C) X (@diagram_family_at_func B WalkingArrow_cat
  C D walking_arrow_src))) (@diagram_family_at_func B WalkingArrow_cat C D walking_arrow_tgt)
  (@one_cat_difference_cospan_transf B C C1 Prod t A T0 X (@diagram_family_at_func B WalkingArrow_cat C D
  walking_arrow_src) (@diagram_family_at_func B WalkingArrow_cat C D walking_arrow_tgt) f (@diagram_family_transf
  B WalkingArrow_cat C D walking_arrow_src walking_arrow_tgt walking_arrow_generator))) (@adjunction_coimage_func
  C (@additive_preadditive C Prod t A) t (@additive_terminal_object C Prod t A) T0 P Q)
  (@diagram_evaluation_at_func WalkingArrow_cat C walking_arrow_tgt)) (@one_cat_adjunction_coimage_to_target C
  (@additive_preadditive C Prod t A) C1 t (@additive_terminal_object C Prod t A) T0 P Q))
  (@omega_equiv_along_left_inv (Functor_cat B C) (@comp_cat_fapp0 B (Functor_cat WalkingArrow_cat C) C
  (@adjunction_coimage_func C (@additive_preadditive C Prod t A) t (@additive_terminal_object C Prod t A) T0 P Q)
  (@transf_arrow_diagram_func B C (@fapp0 (Functor_cat B (Product_cat C C)) (Functor_cat B C) (@comp_cat_cov_func
  B (Product_cat C C) C Prod) (@Struct_sigma (Functor B C) (λ _ : τ (Functor B C), Functor B C) X
  (@diagram_family_at_func B WalkingArrow_cat C D walking_arrow_src))) (@diagram_family_at_func B WalkingArrow_cat
  C D walking_arrow_tgt) (@one_cat_difference_cospan_transf B C C1 Prod t A T0 X (@diagram_family_at_func B
  WalkingArrow_cat C D walking_arrow_src) (@diagram_family_at_func B WalkingArrow_cat C D walking_arrow_tgt) f
  (@diagram_family_transf B WalkingArrow_cat C D walking_arrow_src walking_arrow_tgt walking_arrow_generator))))
  (@diagram_family_at_func B WalkingArrow_cat C D walking_arrow_tgt) (@fapp0 _ _ (@comp_cat_con_fapp1_func B
  (Functor_cat WalkingArrow_cat C) C (@transf_arrow_diagram_func B C (@fapp0 (Functor_cat B (Product_cat C C))
  (Functor_cat B C) (@comp_cat_cov_func B (Product_cat C C) C Prod) (@Struct_sigma (Functor B C) (λ _ : τ (Functor
  B C), Functor B C) X (@diagram_family_at_func B WalkingArrow_cat C D walking_arrow_src)))
  (@diagram_family_at_func B WalkingArrow_cat C D walking_arrow_tgt) (@one_cat_difference_cospan_transf B C C1
  Prod t A T0 X (@diagram_family_at_func B WalkingArrow_cat C D walking_arrow_src) (@diagram_family_at_func B
  WalkingArrow_cat C D walking_arrow_tgt) f (@diagram_family_transf B WalkingArrow_cat C D walking_arrow_src
  walking_arrow_tgt walking_arrow_generator))) (@adjunction_coimage_func C (@additive_preadditive C Prod t A) t
  (@additive_terminal_object C Prod t A) T0 P Q) (@diagram_evaluation_at_func WalkingArrow_cat C
  walking_arrow_tgt)) (@one_cat_adjunction_coimage_to_target C (@additive_preadditive C Prod t A) C1 t
  (@additive_terminal_object C Prod t A) T0 P Q)) (@one_cat_difference_row_cover_omega B C C1 Prod t A T0 P Q N U
  D h R X f))) (@id (Functor_cat B C) (@diagram_family_at_func B WalkingArrow_cat C D walking_arrow_tgt)));
assert [B C : Cat] (C1 : τ (IsNCat (cat_succ cat_zero) C)) [Prod : τ (Functor (Product_cat C C) C)] [t : τ (Obj
  C)] (A : τ (@AdditiveCategory C Prod t)) (T0 : τ (@TerminalObject (Op_cat C) t)) (P : τ
  (@KernelAdjunctionStructure C (@additive_preadditive C Prod t A) t (@additive_terminal_object C Prod t A))) (Q :
  τ (@CokernelAdjunctionStructure C (@additive_preadditive C Prod t A) t T0)) (N : τ (@OneCatAdjunctionNormality C
  (@additive_preadditive C Prod t A) C1 t (@additive_terminal_object C Prod t A) T0 P Q)) (U : τ (Functor B C)) (D
  : τ (Functor B (Functor_cat WalkingArrow_cat C))) (h : τ (@Transf B (Functor_cat WalkingArrow_cat C)
  (@comp_cat_fapp0 B C (Functor_cat WalkingArrow_cat C) (@terminal_arrow_diagram_func C t
  (@additive_terminal_object C Prod t A)) U) D)) (R : τ (@OneCatShortExactFamily B C (@additive_preadditive C Prod
  t A) C1 t (@additive_terminal_object C Prod t A) T0 P Q U D h)) (X : τ (Functor B C)) (f : τ (@Transf B C X
  (@diagram_family_at_func B WalkingArrow_cat C D walking_arrow_tgt))) (i j : τ (Obj B)) ⊢ @tapp1_func B C
  (@diagram_family_at_func B WalkingArrow_cat C D walking_arrow_tgt) (@comp_cat_fapp0 B (Functor_cat
  WalkingArrow_cat C) C (@adjunction_coimage_func C (@additive_preadditive C Prod t A) t
  (@additive_terminal_object C Prod t A) T0 P Q) (@transf_arrow_diagram_func B C (@fapp0 (Functor_cat B
  (Product_cat C C)) (Functor_cat B C) (@comp_cat_cov_func B (Product_cat C C) C Prod) (@Struct_sigma (Functor B
  C) (λ _ : τ (Functor B C), Functor B C) X (@diagram_family_at_func B WalkingArrow_cat C D walking_arrow_src)))
  (@diagram_family_at_func B WalkingArrow_cat C D walking_arrow_tgt) (@one_cat_difference_cospan_transf B C C1
  Prod t A T0 X (@diagram_family_at_func B WalkingArrow_cat C D walking_arrow_src) (@diagram_family_at_func B
  WalkingArrow_cat C D walking_arrow_tgt) f (@diagram_family_transf B WalkingArrow_cat C D walking_arrow_src
  walking_arrow_tgt walking_arrow_generator)))) i j (@omega_equiv_along_left_inv (Functor_cat B C)
  (@comp_cat_fapp0 B (Functor_cat WalkingArrow_cat C) C (@adjunction_coimage_func C (@additive_preadditive C Prod
  t A) t (@additive_terminal_object C Prod t A) T0 P Q) (@transf_arrow_diagram_func B C (@fapp0 (Functor_cat B
  (Product_cat C C)) (Functor_cat B C) (@comp_cat_cov_func B (Product_cat C C) C Prod) (@Struct_sigma (Functor B
  C) (λ _ : τ (Functor B C), Functor B C) X (@diagram_family_at_func B WalkingArrow_cat C D walking_arrow_src)))
  (@diagram_family_at_func B WalkingArrow_cat C D walking_arrow_tgt) (@one_cat_difference_cospan_transf B C C1
  Prod t A T0 X (@diagram_family_at_func B WalkingArrow_cat C D walking_arrow_src) (@diagram_family_at_func B
  WalkingArrow_cat C D walking_arrow_tgt) f (@diagram_family_transf B WalkingArrow_cat C D walking_arrow_src
  walking_arrow_tgt walking_arrow_generator)))) (@diagram_family_at_func B WalkingArrow_cat C D walking_arrow_tgt)
  (@fapp0 _ _ (@comp_cat_con_fapp1_func B (Functor_cat WalkingArrow_cat C) C (@transf_arrow_diagram_func B C
  (@fapp0 (Functor_cat B (Product_cat C C)) (Functor_cat B C) (@comp_cat_cov_func B (Product_cat C C) C Prod)
  (@Struct_sigma (Functor B C) (λ _ : τ (Functor B C), Functor B C) X (@diagram_family_at_func B WalkingArrow_cat
  C D walking_arrow_src))) (@diagram_family_at_func B WalkingArrow_cat C D walking_arrow_tgt)
  (@one_cat_difference_cospan_transf B C C1 Prod t A T0 X (@diagram_family_at_func B WalkingArrow_cat C D
  walking_arrow_src) (@diagram_family_at_func B WalkingArrow_cat C D walking_arrow_tgt) f (@diagram_family_transf
  B WalkingArrow_cat C D walking_arrow_src walking_arrow_tgt walking_arrow_generator))) (@adjunction_coimage_func
  C (@additive_preadditive C Prod t A) t (@additive_terminal_object C Prod t A) T0 P Q)
  (@diagram_evaluation_at_func WalkingArrow_cat C walking_arrow_tgt)) (@one_cat_adjunction_coimage_to_target C
  (@additive_preadditive C Prod t A) C1 t (@additive_terminal_object C Prod t A) T0 P Q))
  (@one_cat_difference_row_cover_omega B C C1 Prod t A T0 P Q N U D h R X f)) : τ (Functor (Hom_cat B i j)
  (Hom_cat C (@fapp0 B C (@diagram_family_at_func B WalkingArrow_cat C D walking_arrow_tgt) i) (@fapp0 B C
  (@comp_cat_fapp0 B (Functor_cat WalkingArrow_cat C) C (@adjunction_coimage_func C (@additive_preadditive C Prod
  t A) t (@additive_terminal_object C Prod t A) T0 P Q) (@transf_arrow_diagram_func B C (@fapp0 (Functor_cat B
  (Product_cat C C)) (Functor_cat B C) (@comp_cat_cov_func B (Product_cat C C) C Prod) (@Struct_sigma (Functor B
  C) (λ _ : τ (Functor B C), Functor B C) X (@diagram_family_at_func B WalkingArrow_cat C D walking_arrow_src)))
  (@diagram_family_at_func B WalkingArrow_cat C D walking_arrow_tgt) (@one_cat_difference_cospan_transf B C C1
  Prod t A T0 X (@diagram_family_at_func B WalkingArrow_cat C D walking_arrow_src) (@diagram_family_at_func B
  WalkingArrow_cat C D walking_arrow_tgt) f (@diagram_family_transf B WalkingArrow_cat C D walking_arrow_src
  walking_arrow_tgt walking_arrow_generator)))) j)));

// Independent whole inputs retain the two original legs through pairing.
assert [B C : Cat] (C1 : τ (IsNCat (cat_succ cat_zero) C)) [Prod : τ (Functor (Product_cat C C) C)] [t : τ (Obj
  C)] (A : τ (@AdditiveCategory C Prod t)) (T0 : τ (@TerminalObject (Op_cat C) t)) (X Y Z : τ (Functor B C)) (f :
  τ (@Transf B C X Z)) (g : τ (@Transf B C Y Z)) (I : τ (Functor B C)) (a : τ (@Transf B C I X)) (b : τ (@Transf B
  C I Y)) ⊢ @one_cat_difference_cospan_pair_path B C C1 Prod t A T0 X Y Z f g I a b : τ (@= (@Transf B C I Z)
  (@comp_fapp0 (Functor_cat B C) I (@fapp0 (Functor_cat B (Product_cat C C)) (Functor_cat B C) (@comp_cat_cov_func
  B (Product_cat C C) C Prod) (@Struct_sigma (Functor B C) (λ _ : τ (Functor B C), Functor B C) X Y)) Z
  (@one_cat_difference_cospan_transf B C C1 Prod t A T0 X Y Z f g) (@one_cat_product_family_pair B C C1 Prod
  (@additive_binary_products C Prod t A) I X Y a b)) (@one_cat_difference_family B C C1 Prod t A T0 I Z
  (@comp_fapp0 (Functor_cat B C) I X Z f a) (@comp_fapp0 (Functor_cat B C) I Y Z g b)));
assert [B C : Cat] (C1 : τ (IsNCat (cat_succ cat_zero) C)) [Prod : τ (Functor (Product_cat C C) C)] [t : τ (Obj
  C)] (A : τ (@AdditiveCategory C Prod t)) (T0 : τ (@TerminalObject (Op_cat C) t)) (P : τ
  (@KernelAdjunctionStructure C (@additive_preadditive C Prod t A) t (@additive_terminal_object C Prod t A))) (Q :
  τ (@CokernelAdjunctionStructure C (@additive_preadditive C Prod t A) t T0)) (U : τ (Functor B C)) (D : τ
  (Functor B (Functor_cat WalkingArrow_cat C))) (h : τ (@Transf B (Functor_cat WalkingArrow_cat C)
  (@comp_cat_fapp0 B C (Functor_cat WalkingArrow_cat C) (@terminal_arrow_diagram_func C t
  (@additive_terminal_object C Prod t A)) U) D)) (R : τ (@OneCatShortExactFamily B C (@additive_preadditive C Prod
  t A) C1 t (@additive_terminal_object C Prod t A) T0 P Q U D h)) (X : τ (Functor B C)) (f : τ (@Transf B C X
  (@diagram_family_at_func B WalkingArrow_cat C D walking_arrow_tgt))) ⊢ @one_cat_difference_row_cokernel_zero B C
  C1 Prod t A T0 P Q U D h R X f : τ (@= (@Transf B C (@diagram_family_at_func B WalkingArrow_cat C D
  walking_arrow_tgt) (@comp_cat_fapp0 B (Functor_cat WalkingArrow_cat C) C (@cokernel_adjunction_func C
  (@additive_preadditive C Prod t A) t T0 Q) (@transf_arrow_diagram_func B C (@fapp0 (Functor_cat B (Product_cat C
  C)) (Functor_cat B C) (@comp_cat_cov_func B (Product_cat C C) C Prod) (@Struct_sigma (Functor B C) (λ _ : τ
  (Functor B C), Functor B C) X (@diagram_family_at_func B WalkingArrow_cat C D walking_arrow_src)))
  (@diagram_family_at_func B WalkingArrow_cat C D walking_arrow_tgt) (@one_cat_difference_cospan_transf B C C1
  Prod t A T0 X (@diagram_family_at_func B WalkingArrow_cat C D walking_arrow_src) (@diagram_family_at_func B
  WalkingArrow_cat C D walking_arrow_tgt) f (@diagram_family_transf B WalkingArrow_cat C D walking_arrow_src
  walking_arrow_tgt walking_arrow_generator))))) (@cokernel_adjunction_family_projection_transf B C
  (@additive_preadditive C Prod t A) t T0 Q (@transf_arrow_diagram_func B C (@fapp0 (Functor_cat B (Product_cat C
  C)) (Functor_cat B C) (@comp_cat_cov_func B (Product_cat C C) C Prod) (@Struct_sigma (Functor B C) (λ _ : τ
  (Functor B C), Functor B C) X (@diagram_family_at_func B WalkingArrow_cat C D walking_arrow_src)))
  (@diagram_family_at_func B WalkingArrow_cat C D walking_arrow_tgt) (@one_cat_difference_cospan_transf B C C1
  Prod t A T0 X (@diagram_family_at_func B WalkingArrow_cat C D walking_arrow_src) (@diagram_family_at_func B
  WalkingArrow_cat C D walking_arrow_tgt) f (@diagram_family_transf B WalkingArrow_cat C D walking_arrow_src
  walking_arrow_tgt walking_arrow_generator)))) (@zero_arrow_family_zero_transf B C t (@additive_terminal_object C
  Prod t A) T0 (@diagram_family_at_func B WalkingArrow_cat C D walking_arrow_tgt) (@comp_cat_fapp0 B (Functor_cat
  WalkingArrow_cat C) C (@cokernel_adjunction_func C (@additive_preadditive C Prod t A) t T0 Q)
  (@transf_arrow_diagram_func B C (@fapp0 (Functor_cat B (Product_cat C C)) (Functor_cat B C) (@comp_cat_cov_func
  B (Product_cat C C) C Prod) (@Struct_sigma (Functor B C) (λ _ : τ (Functor B C), Functor B C) X
  (@diagram_family_at_func B WalkingArrow_cat C D walking_arrow_src))) (@diagram_family_at_func B WalkingArrow_cat
  C D walking_arrow_tgt) (@one_cat_difference_cospan_transf B C C1 Prod t A T0 X (@diagram_family_at_func B
  WalkingArrow_cat C D walking_arrow_src) (@diagram_family_at_func B WalkingArrow_cat C D walking_arrow_tgt) f
  (@diagram_family_transf B WalkingArrow_cat C D walking_arrow_src walking_arrow_tgt
  walking_arrow_generator))))));
assertnot [B C : Cat] (C1 : τ (IsNCat (cat_succ cat_zero) C)) [Prod : τ (Functor (Product_cat C C) C)] [t : τ (Obj
  C)] (A : τ (@AdditiveCategory C Prod t)) (T0 : τ (@TerminalObject (Op_cat C) t)) (P : τ
  (@KernelAdjunctionStructure C (@additive_preadditive C Prod t A) t (@additive_terminal_object C Prod t A))) (Q :
  τ (@CokernelAdjunctionStructure C (@additive_preadditive C Prod t A) t T0)) (N : τ (@OneCatAdjunctionNormality C
  (@additive_preadditive C Prod t A) C1 t (@additive_terminal_object C Prod t A) T0 P Q)) (U : τ (Functor B C)) (D
  : τ (Functor B (Functor_cat WalkingArrow_cat C))) (h : τ (@Transf B (Functor_cat WalkingArrow_cat C)
  (@comp_cat_fapp0 B C (Functor_cat WalkingArrow_cat C) (@terminal_arrow_diagram_func C t
  (@additive_terminal_object C Prod t A)) U) D)) (R : τ (@OneCatShortExactFamily B C (@additive_preadditive C Prod
  t A) C1 t (@additive_terminal_object C Prod t A) T0 P Q U D h)) (X : τ (Functor B C)) (f : τ (@Transf B C X
  (@diagram_family_at_func B WalkingArrow_cat C D walking_arrow_tgt))) (other : τ (@Transf B C (@comp_cat_fapp0 B
  (Functor_cat WalkingArrow_cat C) C (@adjunction_coimage_func C (@additive_preadditive C Prod t A) t
  (@additive_terminal_object C Prod t A) T0 P Q) (@transf_arrow_diagram_func B C (@fapp0 (Functor_cat B
  (Product_cat C C)) (Functor_cat B C) (@comp_cat_cov_func B (Product_cat C C) C Prod) (@Struct_sigma (Functor B
  C) (λ _ : τ (Functor B C), Functor B C) X (@diagram_family_at_func B WalkingArrow_cat C D walking_arrow_src)))
  (@diagram_family_at_func B WalkingArrow_cat C D walking_arrow_tgt) (@one_cat_difference_cospan_transf B C C1
  Prod t A T0 X (@diagram_family_at_func B WalkingArrow_cat C D walking_arrow_src) (@diagram_family_at_func B
  WalkingArrow_cat C D walking_arrow_tgt) f (@diagram_family_transf B WalkingArrow_cat C D walking_arrow_src
  walking_arrow_tgt walking_arrow_generator)))) (@diagram_family_at_func B WalkingArrow_cat C D
  walking_arrow_tgt))) ⊢ (@one_cat_difference_row_cover_omega B C C1 Prod t A T0 P Q N U D h R X f) : τ
  (@OmegaEquivAlong (Functor_cat B C) (@comp_cat_fapp0 B (Functor_cat WalkingArrow_cat C) C
  (@adjunction_coimage_func C (@additive_preadditive C Prod t A) t (@additive_terminal_object C Prod t A) T0 P Q)
  (@transf_arrow_diagram_func B C (@fapp0 (Functor_cat B (Product_cat C C)) (Functor_cat B C) (@comp_cat_cov_func
  B (Product_cat C C) C Prod) (@Struct_sigma (Functor B C) (λ _ : τ (Functor B C), Functor B C) X
  (@diagram_family_at_func B WalkingArrow_cat C D walking_arrow_src))) (@diagram_family_at_func B WalkingArrow_cat
  C D walking_arrow_tgt) (@one_cat_difference_cospan_transf B C C1 Prod t A T0 X (@diagram_family_at_func B
  WalkingArrow_cat C D walking_arrow_src) (@diagram_family_at_func B WalkingArrow_cat C D walking_arrow_tgt) f
  (@diagram_family_transf B WalkingArrow_cat C D walking_arrow_src walking_arrow_tgt walking_arrow_generator))))
  (@diagram_family_at_func B WalkingArrow_cat C D walking_arrow_tgt) other);
assertnot [B C : Cat] (C1 : τ (IsNCat (cat_succ cat_zero) C)) [Prod : τ (Functor (Product_cat C C) C)] [t : τ (Obj
  C)] (A : τ (@AdditiveCategory C Prod t)) (T0 : τ (@TerminalObject (Op_cat C) t)) (X Y Z : τ (Functor B C)) (f :
  τ (@Transf B C X Z)) (g : τ (@Transf B C Y Z)) (f0 : τ (@Transf B C X Z)) ⊢ @eq_refl (@Transf B C (@fapp0
  (Functor_cat B (Product_cat C C)) (Functor_cat B C) (@comp_cat_cov_func B (Product_cat C C) C Prod)
  (@Struct_sigma (Functor B C) (λ _ : τ (Functor B C), Functor B C) X Y)) Z) (@one_cat_difference_cospan_transf B
  C C1 Prod t A T0 X Y Z f g) : τ (@= (@Transf B C (@fapp0 (Functor_cat B (Product_cat C C)) (Functor_cat B C)
  (@comp_cat_cov_func B (Product_cat C C) C Prod) (@Struct_sigma (Functor B C) (λ _ : τ (Functor B C), Functor B
  C) X Y)) Z) (@one_cat_difference_cospan_transf B C C1 Prod t A T0 X Y Z f g) (@one_cat_difference_cospan_transf
  B C C1 Prod t A T0 X Y Z f0 g));
