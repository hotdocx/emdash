require open emdash.emdash3_2_one_cat_difference_cospans;
require open emdash.emdash3_2_one_cat_kernel_family_reconstruction;
require open emdash.emdash3_2_one_cat_kernel_family_restriction_paths;

// Introduce the actual difference of the original kernel inclusion and p.
symbol one_cat_kernel_difference_diagram [B C : Cat] (C1 : τ (IsNCat (cat_succ cat_zero) C)) [Prod : τ
  (Functor (Product_cat C C) C)] [t : τ (Obj C)] (A : τ (@AdditiveCategory C Prod t)) (T0 : τ (@TerminalObject
  (Op_cat C) t)) (P : τ (@KernelAdjunctionStructure C (@additive_preadditive C Prod t A) t
  (@additive_terminal_object C Prod t A))) (M : τ (Functor B C)) (D : τ (Functor B (Functor_cat WalkingArrow_cat
  C))) (p : τ (@Transf B C M (@diagram_family_at_func B WalkingArrow_cat C D walking_arrow_src)))
 : τ (Functor B (Functor_cat WalkingArrow_cat C))
≔ @transf_arrow_diagram_func B C (@fapp0 (Functor_cat B (Product_cat C C)) (Functor_cat B C) (@comp_cat_cov_func B
  (Product_cat C C) C Prod) (@Struct_sigma (Functor B C) (λ _ : τ (Functor B C), Functor B C)
  (@kernel_adjunction_family_func B C (@additive_preadditive C Prod t A) t (@additive_terminal_object C Prod t A)
  P D) M)) (@diagram_family_at_func B WalkingArrow_cat C D walking_arrow_src) (@one_cat_difference_cospan_transf B
  C C1 Prod t A T0 (@kernel_adjunction_family_func B C (@additive_preadditive C Prod t A) t
  (@additive_terminal_object C Prod t A) P D) M (@diagram_family_at_func B WalkingArrow_cat C D walking_arrow_src)
  (@kernel_adjunction_family_inclusion_transf B C (@additive_preadditive C Prod t A) t (@additive_terminal_object
  C Prod t A) P D) p);

// The original auxiliary kernel projects to the original K(D).
symbol one_cat_difference_kernel_first_transf [B C : Cat] (C1 : τ (IsNCat (cat_succ cat_zero) C)) [Prod : τ
  (Functor (Product_cat C C) C)] [t : τ (Obj C)] (A : τ (@AdditiveCategory C Prod t)) (T0 : τ (@TerminalObject
  (Op_cat C) t)) (P : τ (@KernelAdjunctionStructure C (@additive_preadditive C Prod t A) t
  (@additive_terminal_object C Prod t A))) (M : τ (Functor B C)) (D : τ (Functor B (Functor_cat WalkingArrow_cat
  C))) (p : τ (@Transf B C M (@diagram_family_at_func B WalkingArrow_cat C D walking_arrow_src)))
 : τ (@Transf B C (@kernel_adjunction_family_func B C (@additive_preadditive C Prod t A) t
  (@additive_terminal_object C Prod t A) P (@one_cat_kernel_difference_diagram B C C1 Prod t A T0 P M D p))
  (@kernel_adjunction_family_func B C (@additive_preadditive C Prod t A) t (@additive_terminal_object C Prod t A)
  P D))
≔ (@comp_fapp0 (Functor_cat B C) (@kernel_adjunction_family_func B C (@additive_preadditive C Prod t A) t
  (@additive_terminal_object C Prod t A) P (@one_cat_kernel_difference_diagram B C C1 Prod t A T0 P M D p))
  (@fapp0 (Functor_cat B (Product_cat C C)) (Functor_cat B C) (@comp_cat_cov_func B (Product_cat C C) C Prod)
  (@Struct_sigma (Functor B C) (λ _ : τ (Functor B C), Functor B C) (@kernel_adjunction_family_func B C
  (@additive_preadditive C Prod t A) t (@additive_terminal_object C Prod t A) P D) M))
  (@kernel_adjunction_family_func B C (@additive_preadditive C Prod t A) t (@additive_terminal_object C Prod t A)
  P D) (@one_cat_product_family_proj1 B C C1 Prod (@additive_binary_products C Prod t A)
  (@kernel_adjunction_family_func B C (@additive_preadditive C Prod t A) t (@additive_terminal_object C Prod t A)
  P D) M) (@kernel_adjunction_family_inclusion_transf B C (@additive_preadditive C Prod t A) t
  (@additive_terminal_object C Prod t A) P (@one_cat_kernel_difference_diagram B C C1 Prod t A T0 P M D
  p)));

// The same original auxiliary kernel projects to M.
symbol one_cat_difference_kernel_second_transf [B C : Cat] (C1 : τ (IsNCat (cat_succ cat_zero) C)) [Prod : τ
  (Functor (Product_cat C C) C)] [t : τ (Obj C)] (A : τ (@AdditiveCategory C Prod t)) (T0 : τ (@TerminalObject
  (Op_cat C) t)) (P : τ (@KernelAdjunctionStructure C (@additive_preadditive C Prod t A) t
  (@additive_terminal_object C Prod t A))) (M : τ (Functor B C)) (D : τ (Functor B (Functor_cat WalkingArrow_cat
  C))) (p : τ (@Transf B C M (@diagram_family_at_func B WalkingArrow_cat C D walking_arrow_src)))
 : τ (@Transf B C (@kernel_adjunction_family_func B C (@additive_preadditive C Prod t A) t
  (@additive_terminal_object C Prod t A) P (@one_cat_kernel_difference_diagram B C C1 Prod t A T0 P M D p))
  M)
≔ (@comp_fapp0 (Functor_cat B C) (@kernel_adjunction_family_func B C (@additive_preadditive C Prod t A) t
  (@additive_terminal_object C Prod t A) P (@one_cat_kernel_difference_diagram B C C1 Prod t A T0 P M D p))
  (@fapp0 (Functor_cat B (Product_cat C C)) (Functor_cat B C) (@comp_cat_cov_func B (Product_cat C C) C Prod)
  (@Struct_sigma (Functor B C) (λ _ : τ (Functor B C), Functor B C) (@kernel_adjunction_family_func B C
  (@additive_preadditive C Prod t A) t (@additive_terminal_object C Prod t A) P D) M)) M
  (@one_cat_product_family_proj2 B C C1 Prod (@additive_binary_products C Prod t A)
  (@kernel_adjunction_family_func B C (@additive_preadditive C Prod t A) t (@additive_terminal_object C Prod t A)
  P D) M) (@kernel_adjunction_family_inclusion_transf B C (@additive_preadditive C Prod t A) t
  (@additive_terminal_object C Prod t A) P (@one_cat_kernel_difference_diagram B C C1 Prod t A T0 P M D
  p)));

// The auxiliary kernel supplies the compatible pair by whole zero-difference reflection.
symbol one_cat_difference_kernel_compatibility [B C : Cat] (C1 : τ (IsNCat (cat_succ cat_zero) C)) [Prod : τ
  (Functor (Product_cat C C) C)] [t : τ (Obj C)] (A : τ (@AdditiveCategory C Prod t)) (T0 : τ (@TerminalObject
  (Op_cat C) t)) (P : τ (@KernelAdjunctionStructure C (@additive_preadditive C Prod t A) t
  (@additive_terminal_object C Prod t A))) (M : τ (Functor B C)) (D : τ (Functor B (Functor_cat WalkingArrow_cat
  C))) (p : τ (@Transf B C M (@diagram_family_at_func B WalkingArrow_cat C D walking_arrow_src)))
 : τ (@= (@Transf B C (@kernel_adjunction_family_func B C (@additive_preadditive C Prod t A) t
  (@additive_terminal_object C Prod t A) P (@one_cat_kernel_difference_diagram B C C1 Prod t A T0 P M D p))
  (@diagram_family_at_func B WalkingArrow_cat C D walking_arrow_src)) (@comp_fapp0 (Functor_cat B C)
  (@kernel_adjunction_family_func B C (@additive_preadditive C Prod t A) t (@additive_terminal_object C Prod t A)
  P (@one_cat_kernel_difference_diagram B C C1 Prod t A T0 P M D p)) (@kernel_adjunction_family_func B C
  (@additive_preadditive C Prod t A) t (@additive_terminal_object C Prod t A) P D) (@diagram_family_at_func B
  WalkingArrow_cat C D walking_arrow_src) (@kernel_adjunction_family_inclusion_transf B C (@additive_preadditive C
  Prod t A) t (@additive_terminal_object C Prod t A) P D) (@one_cat_difference_kernel_first_transf B C C1
  Prod t A T0 P M D p)) (@comp_fapp0 (Functor_cat B C) (@kernel_adjunction_family_func B C (@additive_preadditive
  C Prod t A) t (@additive_terminal_object C Prod t A) P (@one_cat_kernel_difference_diagram B C C1 Prod t A
  T0 P M D p)) M (@diagram_family_at_func B WalkingArrow_cat C D walking_arrow_src) p
  (@one_cat_difference_kernel_second_transf B C C1 Prod t A T0 P M D p)))
≔ @eq_trans _ _ _ _ (@comp_assoc (Functor_cat B C) (@kernel_adjunction_family_func B C (@additive_preadditive C
  Prod t A) t (@additive_terminal_object C Prod t A) P (@one_cat_kernel_difference_diagram B C C1 Prod t A
  T0 P M D p)) (@fapp0 (Functor_cat B (Product_cat C C)) (Functor_cat B C) (@comp_cat_cov_func B (Product_cat C C)
  C Prod) (@Struct_sigma (Functor B C) (λ _ : τ (Functor B C), Functor B C) (@kernel_adjunction_family_func B C
  (@additive_preadditive C Prod t A) t (@additive_terminal_object C Prod t A) P D) M))
  (@kernel_adjunction_family_func B C (@additive_preadditive C Prod t A) t (@additive_terminal_object C Prod t A)
  P D) (@diagram_family_at_func B WalkingArrow_cat C D walking_arrow_src)
  (@kernel_adjunction_family_inclusion_transf B C (@additive_preadditive C Prod t A) t (@additive_terminal_object
  C Prod t A) P D) (@one_cat_product_family_proj1 B C C1 Prod (@additive_binary_products C Prod t A)
  (@kernel_adjunction_family_func B C (@additive_preadditive C Prod t A) t (@additive_terminal_object C Prod t A)
  P D) M) (@kernel_adjunction_family_inclusion_transf B C (@additive_preadditive C Prod t A) t
  (@additive_terminal_object C Prod t A) P (@one_cat_kernel_difference_diagram B C C1 Prod t A T0 P M D p)))
  (@eq_trans _ _ _ _ (@one_cat_difference_family_zero_reflect B C C1 Prod t A T0 (@kernel_adjunction_family_func B
  C (@additive_preadditive C Prod t A) t (@additive_terminal_object C Prod t A) P
  (@one_cat_kernel_difference_diagram B C C1 Prod t A T0 P M D p)) (@diagram_family_at_func B
  WalkingArrow_cat C D walking_arrow_src) (@comp_fapp0 (Functor_cat B C) (@kernel_adjunction_family_func B C
  (@additive_preadditive C Prod t A) t (@additive_terminal_object C Prod t A) P
  (@one_cat_kernel_difference_diagram B C C1 Prod t A T0 P M D p)) (@fapp0 (Functor_cat B (Product_cat C C))
  (Functor_cat B C) (@comp_cat_cov_func B (Product_cat C C) C Prod) (@Struct_sigma (Functor B C) (λ _ : τ (Functor
  B C), Functor B C) (@kernel_adjunction_family_func B C (@additive_preadditive C Prod t A) t
  (@additive_terminal_object C Prod t A) P D) M)) (@diagram_family_at_func B WalkingArrow_cat C D
  walking_arrow_src) (@comp_fapp0 (Functor_cat B C) (@fapp0 (Functor_cat B (Product_cat C C)) (Functor_cat B C)
  (@comp_cat_cov_func B (Product_cat C C) C Prod) (@Struct_sigma (Functor B C) (λ _ : τ (Functor B C), Functor B
  C) (@kernel_adjunction_family_func B C (@additive_preadditive C Prod t A) t (@additive_terminal_object C Prod t
  A) P D) M)) (@kernel_adjunction_family_func B C (@additive_preadditive C Prod t A) t (@additive_terminal_object
  C Prod t A) P D) (@diagram_family_at_func B WalkingArrow_cat C D walking_arrow_src)
  (@kernel_adjunction_family_inclusion_transf B C (@additive_preadditive C Prod t A) t (@additive_terminal_object
  C Prod t A) P D) (@one_cat_product_family_proj1 B C C1 Prod (@additive_binary_products C Prod t A)
  (@kernel_adjunction_family_func B C (@additive_preadditive C Prod t A) t (@additive_terminal_object C Prod t A)
  P D) M)) (@kernel_adjunction_family_inclusion_transf B C (@additive_preadditive C Prod t A) t
  (@additive_terminal_object C Prod t A) P (@one_cat_kernel_difference_diagram B C C1 Prod t A T0 P M D p)))
  (@comp_fapp0 (Functor_cat B C) (@kernel_adjunction_family_func B C (@additive_preadditive C Prod t A) t
  (@additive_terminal_object C Prod t A) P (@one_cat_kernel_difference_diagram B C C1 Prod t A T0 P M D p))
  (@fapp0 (Functor_cat B (Product_cat C C)) (Functor_cat B C) (@comp_cat_cov_func B (Product_cat C C) C Prod)
  (@Struct_sigma (Functor B C) (λ _ : τ (Functor B C), Functor B C) (@kernel_adjunction_family_func B C
  (@additive_preadditive C Prod t A) t (@additive_terminal_object C Prod t A) P D) M)) (@diagram_family_at_func B
  WalkingArrow_cat C D walking_arrow_src) (@comp_fapp0 (Functor_cat B C) (@fapp0 (Functor_cat B (Product_cat C C))
  (Functor_cat B C) (@comp_cat_cov_func B (Product_cat C C) C Prod) (@Struct_sigma (Functor B C) (λ _ : τ (Functor
  B C), Functor B C) (@kernel_adjunction_family_func B C (@additive_preadditive C Prod t A) t
  (@additive_terminal_object C Prod t A) P D) M)) M (@diagram_family_at_func B WalkingArrow_cat C D
  walking_arrow_src) p (@one_cat_product_family_proj2 B C C1 Prod (@additive_binary_products C Prod t A)
  (@kernel_adjunction_family_func B C (@additive_preadditive C Prod t A) t (@additive_terminal_object C Prod t A)
  P D) M)) (@kernel_adjunction_family_inclusion_transf B C (@additive_preadditive C Prod t A) t
  (@additive_terminal_object C Prod t A) P (@one_cat_kernel_difference_diagram B C C1 Prod t A T0 P M D p)))
  (@eq_trans _ _ _ _ (@eq_sym _ _ _ (@one_cat_difference_family_precompose_path B C C1 Prod t A T0
  (@kernel_adjunction_family_func B C (@additive_preadditive C Prod t A) t (@additive_terminal_object C Prod t A)
  P (@one_cat_kernel_difference_diagram B C C1 Prod t A T0 P M D p)) (@fapp0 (Functor_cat B (Product_cat C
  C)) (Functor_cat B C) (@comp_cat_cov_func B (Product_cat C C) C Prod) (@Struct_sigma (Functor B C) (λ _ : τ
  (Functor B C), Functor B C) (@kernel_adjunction_family_func B C (@additive_preadditive C Prod t A) t
  (@additive_terminal_object C Prod t A) P D) M)) (@diagram_family_at_func B WalkingArrow_cat C D
  walking_arrow_src) (@comp_fapp0 (Functor_cat B C) (@fapp0 (Functor_cat B (Product_cat C C)) (Functor_cat B C)
  (@comp_cat_cov_func B (Product_cat C C) C Prod) (@Struct_sigma (Functor B C) (λ _ : τ (Functor B C), Functor B
  C) (@kernel_adjunction_family_func B C (@additive_preadditive C Prod t A) t (@additive_terminal_object C Prod t
  A) P D) M)) (@kernel_adjunction_family_func B C (@additive_preadditive C Prod t A) t (@additive_terminal_object
  C Prod t A) P D) (@diagram_family_at_func B WalkingArrow_cat C D walking_arrow_src)
  (@kernel_adjunction_family_inclusion_transf B C (@additive_preadditive C Prod t A) t (@additive_terminal_object
  C Prod t A) P D) (@one_cat_product_family_proj1 B C C1 Prod (@additive_binary_products C Prod t A)
  (@kernel_adjunction_family_func B C (@additive_preadditive C Prod t A) t (@additive_terminal_object C Prod t A)
  P D) M)) (@comp_fapp0 (Functor_cat B C) (@fapp0 (Functor_cat B (Product_cat C C)) (Functor_cat B C)
  (@comp_cat_cov_func B (Product_cat C C) C Prod) (@Struct_sigma (Functor B C) (λ _ : τ (Functor B C), Functor B
  C) (@kernel_adjunction_family_func B C (@additive_preadditive C Prod t A) t (@additive_terminal_object C Prod t
  A) P D) M)) M (@diagram_family_at_func B WalkingArrow_cat C D walking_arrow_src) p
  (@one_cat_product_family_proj2 B C C1 Prod (@additive_binary_products C Prod t A)
  (@kernel_adjunction_family_func B C (@additive_preadditive C Prod t A) t (@additive_terminal_object C Prod t A)
  P D) M)) (@kernel_adjunction_family_inclusion_transf B C (@additive_preadditive C Prod t A) t
  (@additive_terminal_object C Prod t A) P (@one_cat_kernel_difference_diagram B C C1 Prod t A T0 P M D
  p)))) (@one_cat_kernel_family_annihilation_path B C (@additive_preadditive C Prod t A) C1 t
  (@additive_terminal_object C Prod t A) T0 P (@one_cat_kernel_difference_diagram B C C1 Prod t A T0 P M D
  p)))) (@eq_sym _ _ _ (@comp_assoc (Functor_cat B C) (@kernel_adjunction_family_func B C (@additive_preadditive C
  Prod t A) t (@additive_terminal_object C Prod t A) P (@one_cat_kernel_difference_diagram B C C1 Prod t A
  T0 P M D p)) (@fapp0 (Functor_cat B (Product_cat C C)) (Functor_cat B C) (@comp_cat_cov_func B (Product_cat C C)
  C Prod) (@Struct_sigma (Functor B C) (λ _ : τ (Functor B C), Functor B C) (@kernel_adjunction_family_func B C
  (@additive_preadditive C Prod t A) t (@additive_terminal_object C Prod t A) P D) M)) M (@diagram_family_at_func
  B WalkingArrow_cat C D walking_arrow_src) p (@one_cat_product_family_proj2 B C C1 Prod
  (@additive_binary_products C Prod t A) (@kernel_adjunction_family_func B C (@additive_preadditive C Prod t A) t
  (@additive_terminal_object C Prod t A) P D) M) (@kernel_adjunction_family_inclusion_transf B C
  (@additive_preadditive C Prod t A) t (@additive_terminal_object C Prod t A) P
  (@one_cat_kernel_difference_diagram B C C1 Prod t A T0 P M D p)))));

// The original differential annihilates p after the second auxiliary projection.
symbol one_cat_difference_kernel_precomposition_zero [B C : Cat] (C1 : τ (IsNCat (cat_succ cat_zero) C))
  [Prod : τ (Functor (Product_cat C C) C)] [t : τ (Obj C)] (A : τ (@AdditiveCategory C Prod t)) (T0 : τ
  (@TerminalObject (Op_cat C) t)) (P : τ (@KernelAdjunctionStructure C (@additive_preadditive C Prod t A) t
  (@additive_terminal_object C Prod t A))) (M : τ (Functor B C)) (D : τ (Functor B (Functor_cat WalkingArrow_cat
  C))) (p : τ (@Transf B C M (@diagram_family_at_func B WalkingArrow_cat C D walking_arrow_src)))
 : τ (@= (@Transf B C (@kernel_adjunction_family_func B C (@additive_preadditive C Prod t A) t
  (@additive_terminal_object C Prod t A) P (@one_cat_kernel_difference_diagram B C C1 Prod t A T0 P M D p))
  (@diagram_family_at_func B WalkingArrow_cat C D walking_arrow_tgt)) (@comp_fapp0 (Functor_cat B C)
  (@kernel_adjunction_family_func B C (@additive_preadditive C Prod t A) t (@additive_terminal_object C Prod t A)
  P (@one_cat_kernel_difference_diagram B C C1 Prod t A T0 P M D p)) M (@diagram_family_at_func B
  WalkingArrow_cat C D walking_arrow_tgt) (@diagram_family_transf B WalkingArrow_cat C
  (@precomposed_diagram_family_func B C M D p) walking_arrow_src walking_arrow_tgt walking_arrow_generator)
  (@one_cat_difference_kernel_second_transf B C C1 Prod t A T0 P M D p)) (@zero_arrow_family_zero_transf B C
  t (@additive_terminal_object C Prod t A) T0 (@kernel_adjunction_family_func B C (@additive_preadditive C Prod t
  A) t (@additive_terminal_object C Prod t A) P (@one_cat_kernel_difference_diagram B C C1 Prod t A T0 P M D
  p)) (@diagram_family_at_func B WalkingArrow_cat C D walking_arrow_tgt)))
≔ @eq_trans _ _ _ _ (@eq_sym _ _ _ (@comp_assoc (Functor_cat B C) (@kernel_adjunction_family_func B C
  (@additive_preadditive C Prod t A) t (@additive_terminal_object C Prod t A) P
  (@one_cat_kernel_difference_diagram B C C1 Prod t A T0 P M D p)) M (@diagram_family_at_func B
  WalkingArrow_cat C D walking_arrow_src) (@diagram_family_at_func B WalkingArrow_cat C D walking_arrow_tgt)
  (@diagram_family_transf B WalkingArrow_cat C D walking_arrow_src walking_arrow_tgt walking_arrow_generator) p
  (@one_cat_difference_kernel_second_transf B C C1 Prod t A T0 P M D p))) (@eq_trans _ _ _ _ (@eq_ap
  (@Transf B C (@kernel_adjunction_family_func B C (@additive_preadditive C Prod t A) t (@additive_terminal_object
  C Prod t A) P (@one_cat_kernel_difference_diagram B C C1 Prod t A T0 P M D p)) (@diagram_family_at_func B
  WalkingArrow_cat C D walking_arrow_src)) (@Transf B C (@kernel_adjunction_family_func B C (@additive_preadditive
  C Prod t A) t (@additive_terminal_object C Prod t A) P (@one_cat_kernel_difference_diagram B C C1 Prod t A
  T0 P M D p)) (@diagram_family_at_func B WalkingArrow_cat C D walking_arrow_tgt)) (λ a : τ (@Transf B C
  (@kernel_adjunction_family_func B C (@additive_preadditive C Prod t A) t (@additive_terminal_object C Prod t A)
  P (@one_cat_kernel_difference_diagram B C C1 Prod t A T0 P M D p)) (@diagram_family_at_func B
  WalkingArrow_cat C D walking_arrow_src)), (@comp_fapp0 (Functor_cat B C) (@kernel_adjunction_family_func B C
  (@additive_preadditive C Prod t A) t (@additive_terminal_object C Prod t A) P
  (@one_cat_kernel_difference_diagram B C C1 Prod t A T0 P M D p)) (@diagram_family_at_func B
  WalkingArrow_cat C D walking_arrow_src) (@diagram_family_at_func B WalkingArrow_cat C D walking_arrow_tgt)
  (@diagram_family_transf B WalkingArrow_cat C D walking_arrow_src walking_arrow_tgt walking_arrow_generator) a))
  (@comp_fapp0 (Functor_cat B C) (@kernel_adjunction_family_func B C (@additive_preadditive C Prod t A) t
  (@additive_terminal_object C Prod t A) P (@one_cat_kernel_difference_diagram B C C1 Prod t A T0 P M D p))
  M (@diagram_family_at_func B WalkingArrow_cat C D walking_arrow_src) p
  (@one_cat_difference_kernel_second_transf B C C1 Prod t A T0 P M D p)) (@comp_fapp0 (Functor_cat B C)
  (@kernel_adjunction_family_func B C (@additive_preadditive C Prod t A) t (@additive_terminal_object C Prod t A)
  P (@one_cat_kernel_difference_diagram B C C1 Prod t A T0 P M D p)) (@kernel_adjunction_family_func B C
  (@additive_preadditive C Prod t A) t (@additive_terminal_object C Prod t A) P D) (@diagram_family_at_func B
  WalkingArrow_cat C D walking_arrow_src) (@kernel_adjunction_family_inclusion_transf B C (@additive_preadditive C
  Prod t A) t (@additive_terminal_object C Prod t A) P D) (@one_cat_difference_kernel_first_transf B C C1
  Prod t A T0 P M D p)) (@eq_sym _ _ _ (@one_cat_difference_kernel_compatibility B C C1 Prod t A T0 P M D
  p))) (@eq_trans _ _ _ _ (@comp_assoc (Functor_cat B C) (@kernel_adjunction_family_func B C
  (@additive_preadditive C Prod t A) t (@additive_terminal_object C Prod t A) P
  (@one_cat_kernel_difference_diagram B C C1 Prod t A T0 P M D p)) (@kernel_adjunction_family_func B C
  (@additive_preadditive C Prod t A) t (@additive_terminal_object C Prod t A) P D) (@diagram_family_at_func B
  WalkingArrow_cat C D walking_arrow_src) (@diagram_family_at_func B WalkingArrow_cat C D walking_arrow_tgt)
  (@diagram_family_transf B WalkingArrow_cat C D walking_arrow_src walking_arrow_tgt walking_arrow_generator)
  (@kernel_adjunction_family_inclusion_transf B C (@additive_preadditive C Prod t A) t (@additive_terminal_object
  C Prod t A) P D) (@one_cat_difference_kernel_first_transf B C C1 Prod t A T0 P M D p)) (@eq_trans _ _ _ _
  (@eq_ap (@Transf B C (@kernel_adjunction_family_func B C (@additive_preadditive C Prod t A) t
  (@additive_terminal_object C Prod t A) P D) (@diagram_family_at_func B WalkingArrow_cat C D walking_arrow_tgt))
  (@Transf B C (@kernel_adjunction_family_func B C (@additive_preadditive C Prod t A) t (@additive_terminal_object
  C Prod t A) P (@one_cat_kernel_difference_diagram B C C1 Prod t A T0 P M D p)) (@diagram_family_at_func B
  WalkingArrow_cat C D walking_arrow_tgt)) (λ a : τ (@Transf B C (@kernel_adjunction_family_func B C
  (@additive_preadditive C Prod t A) t (@additive_terminal_object C Prod t A) P D) (@diagram_family_at_func B
  WalkingArrow_cat C D walking_arrow_tgt)), (@comp_fapp0 (Functor_cat B C) (@kernel_adjunction_family_func B C
  (@additive_preadditive C Prod t A) t (@additive_terminal_object C Prod t A) P
  (@one_cat_kernel_difference_diagram B C C1 Prod t A T0 P M D p)) (@kernel_adjunction_family_func B C
  (@additive_preadditive C Prod t A) t (@additive_terminal_object C Prod t A) P D) (@diagram_family_at_func B
  WalkingArrow_cat C D walking_arrow_tgt) a (@one_cat_difference_kernel_first_transf B C C1 Prod t A T0 P M
  D p))) (@comp_fapp0 (Functor_cat B C) (@kernel_adjunction_family_func B C (@additive_preadditive C Prod t A) t
  (@additive_terminal_object C Prod t A) P D) (@diagram_family_at_func B WalkingArrow_cat C D walking_arrow_src)
  (@diagram_family_at_func B WalkingArrow_cat C D walking_arrow_tgt) (@diagram_family_transf B WalkingArrow_cat C
  D walking_arrow_src walking_arrow_tgt walking_arrow_generator) (@kernel_adjunction_family_inclusion_transf B C
  (@additive_preadditive C Prod t A) t (@additive_terminal_object C Prod t A) P D))
  (@zero_arrow_family_zero_transf B C t (@additive_terminal_object C Prod t A) T0 (@kernel_adjunction_family_func
  B C (@additive_preadditive C Prod t A) t (@additive_terminal_object C Prod t A) P D) (@diagram_family_at_func B
  WalkingArrow_cat C D walking_arrow_tgt)) (@one_cat_kernel_family_annihilation_path B C (@additive_preadditive C
  Prod t A) C1 t (@additive_terminal_object C Prod t A) T0 P D)) (@one_cat_zero_family_precompose_path B C C1 t
  (@additive_terminal_object C Prod t A) T0 (@kernel_adjunction_family_func B C (@additive_preadditive C Prod t A)
  t (@additive_terminal_object C Prod t A) P (@one_cat_kernel_difference_diagram B C C1 Prod t A T0 P M D
  p)) (@kernel_adjunction_family_func B C (@additive_preadditive C Prod t A) t (@additive_terminal_object C Prod t
  A) P D) (@diagram_family_at_func B WalkingArrow_cat C D walking_arrow_tgt)
  (@one_cat_difference_kernel_first_transf B C C1 Prod t A T0 P M D p)))));

// Lift through the original L=K(d∘p) by its native kernel mate.
symbol one_cat_difference_kernel_to_precomposition [B C : Cat] (C1 : τ (IsNCat (cat_succ cat_zero) C)) [Prod
  : τ (Functor (Product_cat C C) C)] [t : τ (Obj C)] (A : τ (@AdditiveCategory C Prod t)) (T0 : τ (@TerminalObject
  (Op_cat C) t)) (P : τ (@KernelAdjunctionStructure C (@additive_preadditive C Prod t A) t
  (@additive_terminal_object C Prod t A))) (M : τ (Functor B C)) (D : τ (Functor B (Functor_cat WalkingArrow_cat
  C))) (p : τ (@Transf B C M (@diagram_family_at_func B WalkingArrow_cat C D walking_arrow_src)))
 : τ (@Transf B C (@kernel_adjunction_family_func B C (@additive_preadditive C Prod t A) t
  (@additive_terminal_object C Prod t A) P (@one_cat_kernel_difference_diagram B C C1 Prod t A T0 P M D p))
  (@kernel_precomposition_family_func B C (@additive_preadditive C Prod t A) t (@additive_terminal_object C Prod t
  A) P M D p))
≔ @one_cat_kernel_family_lift B C (@additive_preadditive C Prod t A) C1 t (@additive_terminal_object C Prod t A)
  T0 P (@kernel_adjunction_family_func B C (@additive_preadditive C Prod t A) t (@additive_terminal_object C Prod
  t A) P (@one_cat_kernel_difference_diagram B C C1 Prod t A T0 P M D p)) (@precomposed_diagram_family_func
  B C M D p) (@one_cat_difference_kernel_second_transf B C C1 Prod t A T0 P M D p)
  (@one_cat_difference_kernel_precomposition_zero B C C1 Prod t A T0 P M D p);

// The original first map of L reconstructs the second auxiliary projection.
symbol one_cat_difference_kernel_lift_first_path [B C : Cat] (C1 : τ (IsNCat (cat_succ cat_zero) C)) [Prod :
  τ (Functor (Product_cat C C) C)] [t : τ (Obj C)] (A : τ (@AdditiveCategory C Prod t)) (T0 : τ (@TerminalObject
  (Op_cat C) t)) (P : τ (@KernelAdjunctionStructure C (@additive_preadditive C Prod t A) t
  (@additive_terminal_object C Prod t A))) (M : τ (Functor B C)) (D : τ (Functor B (Functor_cat WalkingArrow_cat
  C))) (p : τ (@Transf B C M (@diagram_family_at_func B WalkingArrow_cat C D walking_arrow_src)))
 : τ (@= (@Transf B C (@kernel_adjunction_family_func B C (@additive_preadditive C Prod t A) t
  (@additive_terminal_object C Prod t A) P (@one_cat_kernel_difference_diagram B C C1 Prod t A T0 P M D p))
  M) (@comp_fapp0 (Functor_cat B C) (@kernel_adjunction_family_func B C (@additive_preadditive C Prod t A) t
  (@additive_terminal_object C Prod t A) P (@one_cat_kernel_difference_diagram B C C1 Prod t A T0 P M D p))
  (@kernel_precomposition_family_func B C (@additive_preadditive C Prod t A) t (@additive_terminal_object C Prod t
  A) P M D p) M (@kernel_precomposition_first_transf B C (@additive_preadditive C Prod t A) t
  (@additive_terminal_object C Prod t A) P M D p) (@one_cat_difference_kernel_to_precomposition B C C1 Prod
  t A T0 P M D p)) (@one_cat_difference_kernel_second_transf B C C1 Prod t A T0 P M D p))
≔ @one_cat_kernel_family_lift_ambient_reconstruction B C (@additive_preadditive C Prod t A) C1 t
  (@additive_terminal_object C Prod t A) T0 P (@kernel_adjunction_family_func B C (@additive_preadditive C Prod t
  A) t (@additive_terminal_object C Prod t A) P (@one_cat_kernel_difference_diagram B C C1 Prod t A T0 P M D
  p)) (@precomposed_diagram_family_func B C M D p) (@one_cat_difference_kernel_second_transf B C C1 Prod t A
  T0 P M D p) (@one_cat_difference_kernel_precomposition_zero B C C1 Prod t A T0 P M D p);

// Original kernel cancellation identifies the first projection with the existing r after the lift.
symbol one_cat_difference_kernel_lift_second_path [B C : Cat] (C1 : τ (IsNCat (cat_succ cat_zero) C)) [Prod
  : τ (Functor (Product_cat C C) C)] [t : τ (Obj C)] (A : τ (@AdditiveCategory C Prod t)) (T0 : τ (@TerminalObject
  (Op_cat C) t)) (P : τ (@KernelAdjunctionStructure C (@additive_preadditive C Prod t A) t
  (@additive_terminal_object C Prod t A))) (M : τ (Functor B C)) (D : τ (Functor B (Functor_cat WalkingArrow_cat
  C))) (p : τ (@Transf B C M (@diagram_family_at_func B WalkingArrow_cat C D walking_arrow_src)))
 : τ (@= (@Transf B C (@kernel_adjunction_family_func B C (@additive_preadditive C Prod t A) t
  (@additive_terminal_object C Prod t A) P (@one_cat_kernel_difference_diagram B C C1 Prod t A T0 P M D p))
  (@kernel_adjunction_family_func B C (@additive_preadditive C Prod t A) t (@additive_terminal_object C Prod t A)
  P D)) (@comp_fapp0 (Functor_cat B C) (@kernel_adjunction_family_func B C (@additive_preadditive C Prod t A) t
  (@additive_terminal_object C Prod t A) P (@one_cat_kernel_difference_diagram B C C1 Prod t A T0 P M D p))
  (@kernel_precomposition_family_func B C (@additive_preadditive C Prod t A) t (@additive_terminal_object C Prod t
  A) P M D p) (@kernel_adjunction_family_func B C (@additive_preadditive C Prod t A) t (@additive_terminal_object
  C Prod t A) P D) (@one_cat_kernel_precomposition_second_transf B C (@additive_preadditive C Prod t A) C1 t
  (@additive_terminal_object C Prod t A) T0 P M D p) (@one_cat_difference_kernel_to_precomposition B C C1
  Prod t A T0 P M D p)) (@one_cat_difference_kernel_first_transf B C C1 Prod t A T0 P M D p))
≔ @one_cat_kernel_family_inclusion_reflect_path B C (@additive_preadditive C Prod t A) C1 t
  (@additive_terminal_object C Prod t A) T0 P (@kernel_adjunction_family_func B C (@additive_preadditive C Prod t
  A) t (@additive_terminal_object C Prod t A) P (@one_cat_kernel_difference_diagram B C C1 Prod t A T0 P M D
  p)) D (@comp_fapp0 (Functor_cat B C) (@kernel_adjunction_family_func B C (@additive_preadditive C Prod t A) t
  (@additive_terminal_object C Prod t A) P (@one_cat_kernel_difference_diagram B C C1 Prod t A T0 P M D p))
  (@kernel_precomposition_family_func B C (@additive_preadditive C Prod t A) t (@additive_terminal_object C Prod t
  A) P M D p) (@kernel_adjunction_family_func B C (@additive_preadditive C Prod t A) t (@additive_terminal_object
  C Prod t A) P D) (@one_cat_kernel_precomposition_second_transf B C (@additive_preadditive C Prod t A) C1 t
  (@additive_terminal_object C Prod t A) T0 P M D p) (@one_cat_difference_kernel_to_precomposition B C C1
  Prod t A T0 P M D p)) (@one_cat_difference_kernel_first_transf B C C1 Prod t A T0 P M D p) (@eq_trans _ _
  _ _ (@comp_assoc (Functor_cat B C) (@kernel_adjunction_family_func B C (@additive_preadditive C Prod t A) t
  (@additive_terminal_object C Prod t A) P (@one_cat_kernel_difference_diagram B C C1 Prod t A T0 P M D p))
  (@kernel_precomposition_family_func B C (@additive_preadditive C Prod t A) t (@additive_terminal_object C Prod t
  A) P M D p) (@kernel_adjunction_family_func B C (@additive_preadditive C Prod t A) t (@additive_terminal_object
  C Prod t A) P D) (@diagram_family_at_func B WalkingArrow_cat C D walking_arrow_src)
  (@kernel_adjunction_family_inclusion_transf B C (@additive_preadditive C Prod t A) t (@additive_terminal_object
  C Prod t A) P D) (@one_cat_kernel_precomposition_second_transf B C (@additive_preadditive C Prod t A) C1 t
  (@additive_terminal_object C Prod t A) T0 P M D p) (@one_cat_difference_kernel_to_precomposition B C C1
  Prod t A T0 P M D p)) (@eq_trans _ _ _ _ (@eq_ap (@Transf B C (@kernel_precomposition_family_func B C
  (@additive_preadditive C Prod t A) t (@additive_terminal_object C Prod t A) P M D p) (@diagram_family_at_func B
  WalkingArrow_cat C D walking_arrow_src)) (@Transf B C (@kernel_adjunction_family_func B C (@additive_preadditive
  C Prod t A) t (@additive_terminal_object C Prod t A) P (@one_cat_kernel_difference_diagram B C C1 Prod t A
  T0 P M D p)) (@diagram_family_at_func B WalkingArrow_cat C D walking_arrow_src)) (λ a : τ (@Transf B C
  (@kernel_precomposition_family_func B C (@additive_preadditive C Prod t A) t (@additive_terminal_object C Prod t
  A) P M D p) (@diagram_family_at_func B WalkingArrow_cat C D walking_arrow_src)), (@comp_fapp0 (Functor_cat B C)
  (@kernel_adjunction_family_func B C (@additive_preadditive C Prod t A) t (@additive_terminal_object C Prod t A)
  P (@one_cat_kernel_difference_diagram B C C1 Prod t A T0 P M D p)) (@kernel_precomposition_family_func B C
  (@additive_preadditive C Prod t A) t (@additive_terminal_object C Prod t A) P M D p) (@diagram_family_at_func B
  WalkingArrow_cat C D walking_arrow_src) a (@one_cat_difference_kernel_to_precomposition B C C1 Prod t A T0
  P M D p))) (@comp_fapp0 (Functor_cat B C) (@kernel_precomposition_family_func B C (@additive_preadditive C Prod
  t A) t (@additive_terminal_object C Prod t A) P M D p) (@kernel_adjunction_family_func B C
  (@additive_preadditive C Prod t A) t (@additive_terminal_object C Prod t A) P D) (@diagram_family_at_func B
  WalkingArrow_cat C D walking_arrow_src) (@kernel_adjunction_family_inclusion_transf B C (@additive_preadditive C
  Prod t A) t (@additive_terminal_object C Prod t A) P D) (@one_cat_kernel_precomposition_second_transf B C
  (@additive_preadditive C Prod t A) C1 t (@additive_terminal_object C Prod t A) T0 P M D p)) (@comp_fapp0
  (Functor_cat B C) (@kernel_precomposition_family_func B C (@additive_preadditive C Prod t A) t
  (@additive_terminal_object C Prod t A) P M D p) M (@diagram_family_at_func B WalkingArrow_cat C D
  walking_arrow_src) p (@kernel_precomposition_first_transf B C (@additive_preadditive C Prod t A) t
  (@additive_terminal_object C Prod t A) P M D p)) (@one_cat_kernel_precomposition_square_path B C
  (@additive_preadditive C Prod t A) C1 t (@additive_terminal_object C Prod t A) T0 P M D p)) (@eq_trans _ _ _ _
  (@eq_sym _ _ _ (@comp_assoc (Functor_cat B C) (@kernel_adjunction_family_func B C (@additive_preadditive C Prod
  t A) t (@additive_terminal_object C Prod t A) P (@one_cat_kernel_difference_diagram B C C1 Prod t A T0 P M
  D p)) (@kernel_precomposition_family_func B C (@additive_preadditive C Prod t A) t (@additive_terminal_object C
  Prod t A) P M D p) M (@diagram_family_at_func B WalkingArrow_cat C D walking_arrow_src) p
  (@kernel_precomposition_first_transf B C (@additive_preadditive C Prod t A) t (@additive_terminal_object C Prod
  t A) P M D p) (@one_cat_difference_kernel_to_precomposition B C C1 Prod t A T0 P M D p))) (@eq_trans _ _ _
  _ (@eq_ap (@Transf B C (@kernel_adjunction_family_func B C (@additive_preadditive C Prod t A) t
  (@additive_terminal_object C Prod t A) P (@one_cat_kernel_difference_diagram B C C1 Prod t A T0 P M D p))
  M) (@Transf B C (@kernel_adjunction_family_func B C (@additive_preadditive C Prod t A) t
  (@additive_terminal_object C Prod t A) P (@one_cat_kernel_difference_diagram B C C1 Prod t A T0 P M D p))
  (@diagram_family_at_func B WalkingArrow_cat C D walking_arrow_src)) (λ a : τ (@Transf B C
  (@kernel_adjunction_family_func B C (@additive_preadditive C Prod t A) t (@additive_terminal_object C Prod t A)
  P (@one_cat_kernel_difference_diagram B C C1 Prod t A T0 P M D p)) M), (@comp_fapp0 (Functor_cat B C)
  (@kernel_adjunction_family_func B C (@additive_preadditive C Prod t A) t (@additive_terminal_object C Prod t A)
  P (@one_cat_kernel_difference_diagram B C C1 Prod t A T0 P M D p)) M (@diagram_family_at_func B
  WalkingArrow_cat C D walking_arrow_src) p a)) (@comp_fapp0 (Functor_cat B C) (@kernel_adjunction_family_func B C
  (@additive_preadditive C Prod t A) t (@additive_terminal_object C Prod t A) P
  (@one_cat_kernel_difference_diagram B C C1 Prod t A T0 P M D p)) (@kernel_precomposition_family_func B C
  (@additive_preadditive C Prod t A) t (@additive_terminal_object C Prod t A) P M D p) M
  (@kernel_precomposition_first_transf B C (@additive_preadditive C Prod t A) t (@additive_terminal_object C Prod
  t A) P M D p) (@one_cat_difference_kernel_to_precomposition B C C1 Prod t A T0 P M D p))
  (@one_cat_difference_kernel_second_transf B C C1 Prod t A T0 P M D p)
  (@one_cat_difference_kernel_lift_first_path B C C1 Prod t A T0 P M D p)) (@eq_sym _ _ _
  (@one_cat_difference_kernel_compatibility B C C1 Prod t A T0 P M D p))))));
