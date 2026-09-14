require open emdash.emdash3_2_one_cat_zero_cokernel_covers;
require open emdash.emdash3_2_one_cat_difference_cokernels;

// The original short-exact row supplies the canonical categorical difference cover.
symbol one_cat_difference_row_cover_omega [B C : Cat] (C1 : τ (IsNCat (cat_succ cat_zero) C)) [Prod : τ
  (Functor (Product_cat C C) C)] [t : τ (Obj C)] (A : τ (@AdditiveCategory C Prod t)) (T0 : τ (@TerminalObject
  (Op_cat C) t)) (P : τ (@KernelAdjunctionStructure C (@additive_preadditive C Prod t A) t
  (@additive_terminal_object C Prod t A))) (Q : τ (@CokernelAdjunctionStructure C (@additive_preadditive C Prod t
  A) t T0)) (N : τ (@OneCatAdjunctionNormality C (@additive_preadditive C Prod t A) C1 t
  (@additive_terminal_object C Prod t A) T0 P Q)) (U : τ (Functor B C)) (D : τ (Functor B (Functor_cat
  WalkingArrow_cat C))) (h : τ (@Transf B (Functor_cat WalkingArrow_cat C) (@comp_cat_fapp0 B C (Functor_cat
  WalkingArrow_cat C) (@terminal_arrow_diagram_func C t (@additive_terminal_object C Prod t A)) U) D)) (R : τ
  (@OneCatShortExactFamily B C (@additive_preadditive C Prod t A) C1 t (@additive_terminal_object C Prod t A) T0 P
  Q U D h)) (X : τ (Functor B C)) (f : τ (@Transf B C X (@diagram_family_at_func B WalkingArrow_cat C D
  walking_arrow_tgt)))
 : τ (@OmegaEquivAlong (Functor_cat B C) (@comp_cat_fapp0 B (Functor_cat WalkingArrow_cat C) C
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
  (@diagram_family_at_func B WalkingArrow_cat C D walking_arrow_tgt) (@one_cat_difference_cospan_transf B C
  C1 Prod t A T0 X (@diagram_family_at_func B WalkingArrow_cat C D walking_arrow_src) (@diagram_family_at_func B
  WalkingArrow_cat C D walking_arrow_tgt) f (@diagram_family_transf B WalkingArrow_cat C D walking_arrow_src
  walking_arrow_tgt walking_arrow_generator))) (@adjunction_coimage_func C (@additive_preadditive C Prod t A) t
  (@additive_terminal_object C Prod t A) T0 P Q) (@diagram_evaluation_at_func WalkingArrow_cat C
  walking_arrow_tgt)) (@one_cat_adjunction_coimage_to_target C (@additive_preadditive C Prod t A) C1 t
  (@additive_terminal_object C Prod t A) T0 P Q)))
≔ @one_cat_zero_cokernel_cover_omega B C (@additive_preadditive C Prod t A) C1 t (@additive_terminal_object
  C Prod t A) T0 P Q N (@transf_arrow_diagram_func B C (@fapp0 (Functor_cat B (Product_cat C C)) (Functor_cat B C)
  (@comp_cat_cov_func B (Product_cat C C) C Prod) (@Struct_sigma (Functor B C) (λ _ : τ (Functor B C), Functor B
  C) X (@diagram_family_at_func B WalkingArrow_cat C D walking_arrow_src))) (@diagram_family_at_func B
  WalkingArrow_cat C D walking_arrow_tgt) (@one_cat_difference_cospan_transf B C C1 Prod t A T0 X
  (@diagram_family_at_func B WalkingArrow_cat C D walking_arrow_src) (@diagram_family_at_func B WalkingArrow_cat C
  D walking_arrow_tgt) f (@diagram_family_transf B WalkingArrow_cat C D walking_arrow_src walking_arrow_tgt
  walking_arrow_generator))) (@one_cat_difference_row_cokernel_zero B C C1 Prod t A T0 P Q U D h R X f);
