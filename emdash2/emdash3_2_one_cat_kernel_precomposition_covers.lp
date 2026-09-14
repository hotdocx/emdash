require open emdash.emdash3_2_one_cat_kernel_difference_lifts;
require open emdash.emdash3_2_one_cat_difference_cover_closure;
require open emdash.emdash3_2_one_cat_difference_factor_paths;

// Compose the original cokernel of r with the original first product projection.
symbol one_cat_kernel_cover_cokernel_input [B C : Cat] (C1 : τ (IsNCat (cat_succ cat_zero) C)) [Prod : τ
  (Functor (Product_cat C C) C)] [t : τ (Obj C)] (A : τ (@AdditiveCategory C Prod t)) (T0 : τ (@TerminalObject
  (Op_cat C) t)) (P : τ (@KernelAdjunctionStructure C (@additive_preadditive C Prod t A) t
  (@additive_terminal_object C Prod t A))) (Q : τ (@CokernelAdjunctionStructure C (@additive_preadditive C Prod t
  A) t T0)) (M : τ (Functor B C)) (D : τ (Functor B (Functor_cat WalkingArrow_cat C))) (p : τ (@Transf B C M
  (@diagram_family_at_func B WalkingArrow_cat C D walking_arrow_src)))
 : τ (@Transf B C (@fapp0 (Functor_cat B (Product_cat C C)) (Functor_cat B C) (@comp_cat_cov_func B (Product_cat C
  C) C Prod) (@Struct_sigma (Functor B C) (λ _ : τ (Functor B C), Functor B C) (@kernel_adjunction_family_func B C
  (@additive_preadditive C Prod t A) t (@additive_terminal_object C Prod t A) P D) M))
  (@cokernel_adjunction_family_func B C (@additive_preadditive C Prod t A) t T0 Q (@transf_arrow_diagram_func B C
  (@kernel_precomposition_family_func B C (@additive_preadditive C Prod t A) t (@additive_terminal_object C Prod t
  A) P M D p) (@kernel_adjunction_family_func B C (@additive_preadditive C Prod t A) t (@additive_terminal_object
  C Prod t A) P D) (@one_cat_kernel_precomposition_second_transf B C (@additive_preadditive C Prod t A) C1 t
  (@additive_terminal_object C Prod t A) T0 P M D p))))
≔ (@comp_fapp0 (Functor_cat B C) (@fapp0 (Functor_cat B (Product_cat C C)) (Functor_cat B C) (@comp_cat_cov_func B
  (Product_cat C C) C Prod) (@Struct_sigma (Functor B C) (λ _ : τ (Functor B C), Functor B C)
  (@kernel_adjunction_family_func B C (@additive_preadditive C Prod t A) t (@additive_terminal_object C Prod t A)
  P D) M)) (@kernel_adjunction_family_func B C (@additive_preadditive C Prod t A) t (@additive_terminal_object C
  Prod t A) P D) (@cokernel_adjunction_family_func B C (@additive_preadditive C Prod t A) t T0 Q
  (@transf_arrow_diagram_func B C (@kernel_precomposition_family_func B C (@additive_preadditive C Prod t A) t
  (@additive_terminal_object C Prod t A) P M D p) (@kernel_adjunction_family_func B C (@additive_preadditive C
  Prod t A) t (@additive_terminal_object C Prod t A) P D) (@one_cat_kernel_precomposition_second_transf B C
  (@additive_preadditive C Prod t A) C1 t (@additive_terminal_object C Prod t A) T0 P M D p)))
  (@cokernel_adjunction_family_projection_transf B C (@additive_preadditive C Prod t A) t T0 Q
  (@transf_arrow_diagram_func B C (@kernel_precomposition_family_func B C (@additive_preadditive C Prod t A) t
  (@additive_terminal_object C Prod t A) P M D p) (@kernel_adjunction_family_func B C (@additive_preadditive C
  Prod t A) t (@additive_terminal_object C Prod t A) P D) (@one_cat_kernel_precomposition_second_transf B C
  (@additive_preadditive C Prod t A) C1 t (@additive_terminal_object C Prod t A) T0 P M D p)))
  (@one_cat_product_family_proj1 B C C1 Prod (@additive_binary_products C Prod t A)
  (@kernel_adjunction_family_func B C (@additive_preadditive C Prod t A) t (@additive_terminal_object C Prod t A)
  P D) M));

// Its auxiliary-kernel annihilation follows through the proved lift into the original L.
symbol one_cat_kernel_cover_cokernel_input_zero [B C : Cat] (C1 : τ (IsNCat (cat_succ cat_zero) C)) [Prod :
  τ (Functor (Product_cat C C) C)] [t : τ (Obj C)] (A : τ (@AdditiveCategory C Prod t)) (T0 : τ (@TerminalObject
  (Op_cat C) t)) (P : τ (@KernelAdjunctionStructure C (@additive_preadditive C Prod t A) t
  (@additive_terminal_object C Prod t A))) (Q : τ (@CokernelAdjunctionStructure C (@additive_preadditive C Prod t
  A) t T0)) (M : τ (Functor B C)) (D : τ (Functor B (Functor_cat WalkingArrow_cat C))) (p : τ (@Transf B C M
  (@diagram_family_at_func B WalkingArrow_cat C D walking_arrow_src)))
 : τ (@= (@Transf B C (@kernel_adjunction_family_func B C (@additive_preadditive C Prod t A) t
  (@additive_terminal_object C Prod t A) P (@one_cat_kernel_difference_diagram B C C1 Prod t A T0 P M D p))
  (@cokernel_adjunction_family_func B C (@additive_preadditive C Prod t A) t T0 Q (@transf_arrow_diagram_func B C
  (@kernel_precomposition_family_func B C (@additive_preadditive C Prod t A) t (@additive_terminal_object C Prod t
  A) P M D p) (@kernel_adjunction_family_func B C (@additive_preadditive C Prod t A) t (@additive_terminal_object
  C Prod t A) P D) (@one_cat_kernel_precomposition_second_transf B C (@additive_preadditive C Prod t A) C1 t
  (@additive_terminal_object C Prod t A) T0 P M D p)))) (@comp_fapp0 (Functor_cat B C)
  (@kernel_adjunction_family_func B C (@additive_preadditive C Prod t A) t (@additive_terminal_object C Prod t A)
  P (@one_cat_kernel_difference_diagram B C C1 Prod t A T0 P M D p)) (@fapp0 (Functor_cat B (Product_cat C
  C)) (Functor_cat B C) (@comp_cat_cov_func B (Product_cat C C) C Prod) (@Struct_sigma (Functor B C) (λ _ : τ
  (Functor B C), Functor B C) (@kernel_adjunction_family_func B C (@additive_preadditive C Prod t A) t
  (@additive_terminal_object C Prod t A) P D) M)) (@cokernel_adjunction_family_func B C (@additive_preadditive C
  Prod t A) t T0 Q (@transf_arrow_diagram_func B C (@kernel_precomposition_family_func B C (@additive_preadditive
  C Prod t A) t (@additive_terminal_object C Prod t A) P M D p) (@kernel_adjunction_family_func B C
  (@additive_preadditive C Prod t A) t (@additive_terminal_object C Prod t A) P D)
  (@one_cat_kernel_precomposition_second_transf B C (@additive_preadditive C Prod t A) C1 t
  (@additive_terminal_object C Prod t A) T0 P M D p))) (@one_cat_kernel_cover_cokernel_input B C C1 Prod t A
  T0 P Q M D p) (@kernel_adjunction_family_inclusion_transf B C (@additive_preadditive C Prod t A) t
  (@additive_terminal_object C Prod t A) P (@one_cat_kernel_difference_diagram B C C1 Prod t A T0 P M D p)))
  (@zero_arrow_family_zero_transf B C t (@additive_terminal_object C Prod t A) T0 (@kernel_adjunction_family_func
  B C (@additive_preadditive C Prod t A) t (@additive_terminal_object C Prod t A) P
  (@one_cat_kernel_difference_diagram B C C1 Prod t A T0 P M D p)) (@cokernel_adjunction_family_func B C
  (@additive_preadditive C Prod t A) t T0 Q (@transf_arrow_diagram_func B C (@kernel_precomposition_family_func B
  C (@additive_preadditive C Prod t A) t (@additive_terminal_object C Prod t A) P M D p)
  (@kernel_adjunction_family_func B C (@additive_preadditive C Prod t A) t (@additive_terminal_object C Prod t A)
  P D) (@one_cat_kernel_precomposition_second_transf B C (@additive_preadditive C Prod t A) C1 t
  (@additive_terminal_object C Prod t A) T0 P M D p)))))
≔ (@eq_trans _ _ _ _ (@eq_sym _ _ _ (@comp_assoc (Functor_cat B C) (@kernel_adjunction_family_func B C
  (@additive_preadditive C Prod t A) t (@additive_terminal_object C Prod t A) P
  (@one_cat_kernel_difference_diagram B C C1 Prod t A T0 P M D p)) (@fapp0 (Functor_cat B (Product_cat C C))
  (Functor_cat B C) (@comp_cat_cov_func B (Product_cat C C) C Prod) (@Struct_sigma (Functor B C) (λ _ : τ (Functor
  B C), Functor B C) (@kernel_adjunction_family_func B C (@additive_preadditive C Prod t A) t
  (@additive_terminal_object C Prod t A) P D) M)) (@kernel_adjunction_family_func B C (@additive_preadditive C
  Prod t A) t (@additive_terminal_object C Prod t A) P D) (@cokernel_adjunction_family_func B C
  (@additive_preadditive C Prod t A) t T0 Q (@transf_arrow_diagram_func B C (@kernel_precomposition_family_func B
  C (@additive_preadditive C Prod t A) t (@additive_terminal_object C Prod t A) P M D p)
  (@kernel_adjunction_family_func B C (@additive_preadditive C Prod t A) t (@additive_terminal_object C Prod t A)
  P D) (@one_cat_kernel_precomposition_second_transf B C (@additive_preadditive C Prod t A) C1 t
  (@additive_terminal_object C Prod t A) T0 P M D p))) (@cokernel_adjunction_family_projection_transf B C
  (@additive_preadditive C Prod t A) t T0 Q (@transf_arrow_diagram_func B C (@kernel_precomposition_family_func B
  C (@additive_preadditive C Prod t A) t (@additive_terminal_object C Prod t A) P M D p)
  (@kernel_adjunction_family_func B C (@additive_preadditive C Prod t A) t (@additive_terminal_object C Prod t A)
  P D) (@one_cat_kernel_precomposition_second_transf B C (@additive_preadditive C Prod t A) C1 t
  (@additive_terminal_object C Prod t A) T0 P M D p))) (@one_cat_product_family_proj1 B C C1 Prod
  (@additive_binary_products C Prod t A) (@kernel_adjunction_family_func B C (@additive_preadditive C Prod t A) t
  (@additive_terminal_object C Prod t A) P D) M) (@kernel_adjunction_family_inclusion_transf B C
  (@additive_preadditive C Prod t A) t (@additive_terminal_object C Prod t A) P
  (@one_cat_kernel_difference_diagram B C C1 Prod t A T0 P M D p)))) (@eq_trans _ _ _ _ (@eq_ap (@Transf B C
  (@kernel_adjunction_family_func B C (@additive_preadditive C Prod t A) t (@additive_terminal_object C Prod t A)
  P (@one_cat_kernel_difference_diagram B C C1 Prod t A T0 P M D p)) (@kernel_adjunction_family_func B C
  (@additive_preadditive C Prod t A) t (@additive_terminal_object C Prod t A) P D)) (@Transf B C
  (@kernel_adjunction_family_func B C (@additive_preadditive C Prod t A) t (@additive_terminal_object C Prod t A)
  P (@one_cat_kernel_difference_diagram B C C1 Prod t A T0 P M D p)) (@cokernel_adjunction_family_func B C
  (@additive_preadditive C Prod t A) t T0 Q (@transf_arrow_diagram_func B C (@kernel_precomposition_family_func B
  C (@additive_preadditive C Prod t A) t (@additive_terminal_object C Prod t A) P M D p)
  (@kernel_adjunction_family_func B C (@additive_preadditive C Prod t A) t (@additive_terminal_object C Prod t A)
  P D) (@one_cat_kernel_precomposition_second_transf B C (@additive_preadditive C Prod t A) C1 t
  (@additive_terminal_object C Prod t A) T0 P M D p)))) (λ a : τ (@Transf B C (@kernel_adjunction_family_func B C
  (@additive_preadditive C Prod t A) t (@additive_terminal_object C Prod t A) P
  (@one_cat_kernel_difference_diagram B C C1 Prod t A T0 P M D p)) (@kernel_adjunction_family_func B C
  (@additive_preadditive C Prod t A) t (@additive_terminal_object C Prod t A) P D)), (@comp_fapp0 (Functor_cat B
  C) (@kernel_adjunction_family_func B C (@additive_preadditive C Prod t A) t (@additive_terminal_object C Prod t
  A) P (@one_cat_kernel_difference_diagram B C C1 Prod t A T0 P M D p)) (@kernel_adjunction_family_func B C
  (@additive_preadditive C Prod t A) t (@additive_terminal_object C Prod t A) P D)
  (@cokernel_adjunction_family_func B C (@additive_preadditive C Prod t A) t T0 Q (@transf_arrow_diagram_func B C
  (@kernel_precomposition_family_func B C (@additive_preadditive C Prod t A) t (@additive_terminal_object C Prod t
  A) P M D p) (@kernel_adjunction_family_func B C (@additive_preadditive C Prod t A) t (@additive_terminal_object
  C Prod t A) P D) (@one_cat_kernel_precomposition_second_transf B C (@additive_preadditive C Prod t A) C1 t
  (@additive_terminal_object C Prod t A) T0 P M D p))) (@cokernel_adjunction_family_projection_transf B C
  (@additive_preadditive C Prod t A) t T0 Q (@transf_arrow_diagram_func B C (@kernel_precomposition_family_func B
  C (@additive_preadditive C Prod t A) t (@additive_terminal_object C Prod t A) P M D p)
  (@kernel_adjunction_family_func B C (@additive_preadditive C Prod t A) t (@additive_terminal_object C Prod t A)
  P D) (@one_cat_kernel_precomposition_second_transf B C (@additive_preadditive C Prod t A) C1 t
  (@additive_terminal_object C Prod t A) T0 P M D p))) a)) (@one_cat_difference_kernel_first_transf B C C1
  Prod t A T0 P M D p) (@comp_fapp0 (Functor_cat B C) (@kernel_adjunction_family_func B C (@additive_preadditive C
  Prod t A) t (@additive_terminal_object C Prod t A) P (@one_cat_kernel_difference_diagram B C C1 Prod t A
  T0 P M D p)) (@kernel_precomposition_family_func B C (@additive_preadditive C Prod t A) t
  (@additive_terminal_object C Prod t A) P M D p) (@kernel_adjunction_family_func B C (@additive_preadditive C
  Prod t A) t (@additive_terminal_object C Prod t A) P D) (@one_cat_kernel_precomposition_second_transf B C
  (@additive_preadditive C Prod t A) C1 t (@additive_terminal_object C Prod t A) T0 P M D p)
  (@one_cat_difference_kernel_to_precomposition B C C1 Prod t A T0 P M D p)) (@eq_sym _ _ _
  (@one_cat_difference_kernel_lift_second_path B C C1 Prod t A T0 P M D p))) (@eq_trans _ _ _ _ (@comp_assoc
  (Functor_cat B C) (@kernel_adjunction_family_func B C (@additive_preadditive C Prod t A) t
  (@additive_terminal_object C Prod t A) P (@one_cat_kernel_difference_diagram B C C1 Prod t A T0 P M D p))
  (@kernel_precomposition_family_func B C (@additive_preadditive C Prod t A) t (@additive_terminal_object C Prod t
  A) P M D p) (@kernel_adjunction_family_func B C (@additive_preadditive C Prod t A) t (@additive_terminal_object
  C Prod t A) P D) (@cokernel_adjunction_family_func B C (@additive_preadditive C Prod t A) t T0 Q
  (@transf_arrow_diagram_func B C (@kernel_precomposition_family_func B C (@additive_preadditive C Prod t A) t
  (@additive_terminal_object C Prod t A) P M D p) (@kernel_adjunction_family_func B C (@additive_preadditive C
  Prod t A) t (@additive_terminal_object C Prod t A) P D) (@one_cat_kernel_precomposition_second_transf B C
  (@additive_preadditive C Prod t A) C1 t (@additive_terminal_object C Prod t A) T0 P M D p)))
  (@cokernel_adjunction_family_projection_transf B C (@additive_preadditive C Prod t A) t T0 Q
  (@transf_arrow_diagram_func B C (@kernel_precomposition_family_func B C (@additive_preadditive C Prod t A) t
  (@additive_terminal_object C Prod t A) P M D p) (@kernel_adjunction_family_func B C (@additive_preadditive C
  Prod t A) t (@additive_terminal_object C Prod t A) P D) (@one_cat_kernel_precomposition_second_transf B C
  (@additive_preadditive C Prod t A) C1 t (@additive_terminal_object C Prod t A) T0 P M D p)))
  (@one_cat_kernel_precomposition_second_transf B C (@additive_preadditive C Prod t A) C1 t
  (@additive_terminal_object C Prod t A) T0 P M D p) (@one_cat_difference_kernel_to_precomposition B C C1
  Prod t A T0 P M D p)) (@eq_trans _ _ _ _ (@eq_ap (@Transf B C (@kernel_precomposition_family_func B C
  (@additive_preadditive C Prod t A) t (@additive_terminal_object C Prod t A) P M D p)
  (@cokernel_adjunction_family_func B C (@additive_preadditive C Prod t A) t T0 Q (@transf_arrow_diagram_func B C
  (@kernel_precomposition_family_func B C (@additive_preadditive C Prod t A) t (@additive_terminal_object C Prod t
  A) P M D p) (@kernel_adjunction_family_func B C (@additive_preadditive C Prod t A) t (@additive_terminal_object
  C Prod t A) P D) (@one_cat_kernel_precomposition_second_transf B C (@additive_preadditive C Prod t A) C1 t
  (@additive_terminal_object C Prod t A) T0 P M D p)))) (@Transf B C (@kernel_adjunction_family_func B C
  (@additive_preadditive C Prod t A) t (@additive_terminal_object C Prod t A) P
  (@one_cat_kernel_difference_diagram B C C1 Prod t A T0 P M D p)) (@cokernel_adjunction_family_func B C
  (@additive_preadditive C Prod t A) t T0 Q (@transf_arrow_diagram_func B C (@kernel_precomposition_family_func B
  C (@additive_preadditive C Prod t A) t (@additive_terminal_object C Prod t A) P M D p)
  (@kernel_adjunction_family_func B C (@additive_preadditive C Prod t A) t (@additive_terminal_object C Prod t A)
  P D) (@one_cat_kernel_precomposition_second_transf B C (@additive_preadditive C Prod t A) C1 t
  (@additive_terminal_object C Prod t A) T0 P M D p)))) (λ a : τ (@Transf B C (@kernel_precomposition_family_func
  B C (@additive_preadditive C Prod t A) t (@additive_terminal_object C Prod t A) P M D p)
  (@cokernel_adjunction_family_func B C (@additive_preadditive C Prod t A) t T0 Q (@transf_arrow_diagram_func B C
  (@kernel_precomposition_family_func B C (@additive_preadditive C Prod t A) t (@additive_terminal_object C Prod t
  A) P M D p) (@kernel_adjunction_family_func B C (@additive_preadditive C Prod t A) t (@additive_terminal_object
  C Prod t A) P D) (@one_cat_kernel_precomposition_second_transf B C (@additive_preadditive C Prod t A) C1 t
  (@additive_terminal_object C Prod t A) T0 P M D p)))), (@comp_fapp0 (Functor_cat B C)
  (@kernel_adjunction_family_func B C (@additive_preadditive C Prod t A) t (@additive_terminal_object C Prod t A)
  P (@one_cat_kernel_difference_diagram B C C1 Prod t A T0 P M D p)) (@kernel_precomposition_family_func B C
  (@additive_preadditive C Prod t A) t (@additive_terminal_object C Prod t A) P M D p)
  (@cokernel_adjunction_family_func B C (@additive_preadditive C Prod t A) t T0 Q (@transf_arrow_diagram_func B C
  (@kernel_precomposition_family_func B C (@additive_preadditive C Prod t A) t (@additive_terminal_object C Prod t
  A) P M D p) (@kernel_adjunction_family_func B C (@additive_preadditive C Prod t A) t (@additive_terminal_object
  C Prod t A) P D) (@one_cat_kernel_precomposition_second_transf B C (@additive_preadditive C Prod t A) C1 t
  (@additive_terminal_object C Prod t A) T0 P M D p))) a (@one_cat_difference_kernel_to_precomposition B C
  C1 Prod t A T0 P M D p))) (@comp_fapp0 (Functor_cat B C) (@kernel_precomposition_family_func B C
  (@additive_preadditive C Prod t A) t (@additive_terminal_object C Prod t A) P M D p)
  (@kernel_adjunction_family_func B C (@additive_preadditive C Prod t A) t (@additive_terminal_object C Prod t A)
  P D) (@cokernel_adjunction_family_func B C (@additive_preadditive C Prod t A) t T0 Q (@transf_arrow_diagram_func
  B C (@kernel_precomposition_family_func B C (@additive_preadditive C Prod t A) t (@additive_terminal_object C
  Prod t A) P M D p) (@kernel_adjunction_family_func B C (@additive_preadditive C Prod t A) t
  (@additive_terminal_object C Prod t A) P D) (@one_cat_kernel_precomposition_second_transf B C
  (@additive_preadditive C Prod t A) C1 t (@additive_terminal_object C Prod t A) T0 P M D p)))
  (@cokernel_adjunction_family_projection_transf B C (@additive_preadditive C Prod t A) t T0 Q
  (@transf_arrow_diagram_func B C (@kernel_precomposition_family_func B C (@additive_preadditive C Prod t A) t
  (@additive_terminal_object C Prod t A) P M D p) (@kernel_adjunction_family_func B C (@additive_preadditive C
  Prod t A) t (@additive_terminal_object C Prod t A) P D) (@one_cat_kernel_precomposition_second_transf B C
  (@additive_preadditive C Prod t A) C1 t (@additive_terminal_object C Prod t A) T0 P M D p)))
  (@one_cat_kernel_precomposition_second_transf B C (@additive_preadditive C Prod t A) C1 t
  (@additive_terminal_object C Prod t A) T0 P M D p)) (@zero_arrow_family_zero_transf B C t
  (@additive_terminal_object C Prod t A) T0 (@kernel_precomposition_family_func B C (@additive_preadditive C Prod
  t A) t (@additive_terminal_object C Prod t A) P M D p) (@cokernel_adjunction_family_func B C
  (@additive_preadditive C Prod t A) t T0 Q (@transf_arrow_diagram_func B C (@kernel_precomposition_family_func B
  C (@additive_preadditive C Prod t A) t (@additive_terminal_object C Prod t A) P M D p)
  (@kernel_adjunction_family_func B C (@additive_preadditive C Prod t A) t (@additive_terminal_object C Prod t A)
  P D) (@one_cat_kernel_precomposition_second_transf B C (@additive_preadditive C Prod t A) C1 t
  (@additive_terminal_object C Prod t A) T0 P M D p)))) (@one_cat_cokernel_family_annihilation_path B C
  (@additive_preadditive C Prod t A) C1 t (@additive_terminal_object C Prod t A) T0 Q (@transf_arrow_diagram_func
  B C (@kernel_precomposition_family_func B C (@additive_preadditive C Prod t A) t (@additive_terminal_object C
  Prod t A) P M D p) (@kernel_adjunction_family_func B C (@additive_preadditive C Prod t A) t
  (@additive_terminal_object C Prod t A) P D) (@one_cat_kernel_precomposition_second_transf B C
  (@additive_preadditive C Prod t A) C1 t (@additive_terminal_object C Prod t A) T0 P M D p))))
  (@one_cat_zero_family_precompose_path B C C1 t (@additive_terminal_object C Prod t A) T0
  (@kernel_adjunction_family_func B C (@additive_preadditive C Prod t A) t (@additive_terminal_object C Prod t A)
  P (@one_cat_kernel_difference_diagram B C C1 Prod t A T0 P M D p)) (@kernel_precomposition_family_func B C
  (@additive_preadditive C Prod t A) t (@additive_terminal_object C Prod t A) P M D p)
  (@cokernel_adjunction_family_func B C (@additive_preadditive C Prod t A) t T0 Q (@transf_arrow_diagram_func B C
  (@kernel_precomposition_family_func B C (@additive_preadditive C Prod t A) t (@additive_terminal_object C Prod t
  A) P M D p) (@kernel_adjunction_family_func B C (@additive_preadditive C Prod t A) t (@additive_terminal_object
  C Prod t A) P D) (@one_cat_kernel_precomposition_second_transf B C (@additive_preadditive C Prod t A) C1 t
  (@additive_terminal_object C Prod t A) T0 P M D p))) (@one_cat_difference_kernel_to_precomposition B C C1
  Prod t A T0 P M D p))))));

// Descend that actual map through the derived auxiliary difference cover.
symbol one_cat_kernel_cover_cokernel_descent [B C : Cat] (C1 : τ (IsNCat (cat_succ cat_zero) C)) [Prod : τ
  (Functor (Product_cat C C) C)] [t : τ (Obj C)] (A : τ (@AdditiveCategory C Prod t)) (T0 : τ (@TerminalObject
  (Op_cat C) t)) (P : τ (@KernelAdjunctionStructure C (@additive_preadditive C Prod t A) t
  (@additive_terminal_object C Prod t A))) (Q : τ (@CokernelAdjunctionStructure C (@additive_preadditive C Prod t
  A) t T0)) (N : τ (@OneCatAdjunctionNormality C (@additive_preadditive C Prod t A) C1 t
  (@additive_terminal_object C Prod t A) T0 P Q)) (M : τ (Functor B C)) (D : τ (Functor B (Functor_cat
  WalkingArrow_cat C))) (p : τ (@Transf B C M (@diagram_family_at_func B WalkingArrow_cat C D walking_arrow_src)))
  (zp : τ (@= (@Transf B C (@diagram_family_at_func B WalkingArrow_cat C D walking_arrow_src)
  (@cokernel_adjunction_family_func B C (@additive_preadditive C Prod t A) t T0 Q (@transf_arrow_diagram_func B C
  M (@diagram_family_at_func B WalkingArrow_cat C D walking_arrow_src) p)))
  (@cokernel_adjunction_family_projection_transf B C (@additive_preadditive C Prod t A) t T0 Q
  (@transf_arrow_diagram_func B C M (@diagram_family_at_func B WalkingArrow_cat C D walking_arrow_src) p))
  (@zero_arrow_family_zero_transf B C t (@additive_terminal_object C Prod t A) T0 (@diagram_family_at_func B
  WalkingArrow_cat C D walking_arrow_src) (@cokernel_adjunction_family_func B C (@additive_preadditive C Prod t A)
  t T0 Q (@transf_arrow_diagram_func B C M (@diagram_family_at_func B WalkingArrow_cat C D walking_arrow_src)
  p)))))
 : τ (@Transf B C (@diagram_family_at_func B WalkingArrow_cat C D walking_arrow_src)
  (@cokernel_adjunction_family_func B C (@additive_preadditive C Prod t A) t T0 Q (@transf_arrow_diagram_func B C
  (@kernel_precomposition_family_func B C (@additive_preadditive C Prod t A) t (@additive_terminal_object C Prod t
  A) P M D p) (@kernel_adjunction_family_func B C (@additive_preadditive C Prod t A) t (@additive_terminal_object
  C Prod t A) P D) (@one_cat_kernel_precomposition_second_transf B C (@additive_preadditive C Prod t A) C1 t
  (@additive_terminal_object C Prod t A) T0 P M D p))))
≔ @one_cat_coimage_cover_descent B C (@additive_preadditive C Prod t A) C1 t (@additive_terminal_object C
  Prod t A) T0 P Q (@one_cat_kernel_difference_diagram B C C1 Prod t A T0 P M D p)
  (@one_cat_difference_cospan_zero_cokernel_cover B C C1 Prod t A T0 P Q N (@kernel_adjunction_family_func B
  C (@additive_preadditive C Prod t A) t (@additive_terminal_object C Prod t A) P D) M (@diagram_family_at_func B
  WalkingArrow_cat C D walking_arrow_src) (@kernel_adjunction_family_inclusion_transf B C (@additive_preadditive C
  Prod t A) t (@additive_terminal_object C Prod t A) P D) p zp) (@cokernel_adjunction_family_func B C
  (@additive_preadditive C Prod t A) t T0 Q (@transf_arrow_diagram_func B C (@kernel_precomposition_family_func B
  C (@additive_preadditive C Prod t A) t (@additive_terminal_object C Prod t A) P M D p)
  (@kernel_adjunction_family_func B C (@additive_preadditive C Prod t A) t (@additive_terminal_object C Prod t A)
  P D) (@one_cat_kernel_precomposition_second_transf B C (@additive_preadditive C Prod t A) C1 t
  (@additive_terminal_object C Prod t A) T0 P M D p))) (@one_cat_kernel_cover_cokernel_input B C C1 Prod t A
  T0 P Q M D p) (@one_cat_kernel_cover_cokernel_input_zero B C C1 Prod t A T0 P Q M D p);

// The descended map reconstructs the original cokernel input after the actual difference.
symbol one_cat_kernel_cover_cokernel_descent_path [B C : Cat] (C1 : τ (IsNCat (cat_succ cat_zero) C)) [Prod
  : τ (Functor (Product_cat C C) C)] [t : τ (Obj C)] (A : τ (@AdditiveCategory C Prod t)) (T0 : τ (@TerminalObject
  (Op_cat C) t)) (P : τ (@KernelAdjunctionStructure C (@additive_preadditive C Prod t A) t
  (@additive_terminal_object C Prod t A))) (Q : τ (@CokernelAdjunctionStructure C (@additive_preadditive C Prod t
  A) t T0)) (N : τ (@OneCatAdjunctionNormality C (@additive_preadditive C Prod t A) C1 t
  (@additive_terminal_object C Prod t A) T0 P Q)) (M : τ (Functor B C)) (D : τ (Functor B (Functor_cat
  WalkingArrow_cat C))) (p : τ (@Transf B C M (@diagram_family_at_func B WalkingArrow_cat C D walking_arrow_src)))
  (zp : τ (@= (@Transf B C (@diagram_family_at_func B WalkingArrow_cat C D walking_arrow_src)
  (@cokernel_adjunction_family_func B C (@additive_preadditive C Prod t A) t T0 Q (@transf_arrow_diagram_func B C
  M (@diagram_family_at_func B WalkingArrow_cat C D walking_arrow_src) p)))
  (@cokernel_adjunction_family_projection_transf B C (@additive_preadditive C Prod t A) t T0 Q
  (@transf_arrow_diagram_func B C M (@diagram_family_at_func B WalkingArrow_cat C D walking_arrow_src) p))
  (@zero_arrow_family_zero_transf B C t (@additive_terminal_object C Prod t A) T0 (@diagram_family_at_func B
  WalkingArrow_cat C D walking_arrow_src) (@cokernel_adjunction_family_func B C (@additive_preadditive C Prod t A)
  t T0 Q (@transf_arrow_diagram_func B C M (@diagram_family_at_func B WalkingArrow_cat C D walking_arrow_src)
  p)))))
 : τ (@= (@Transf B C (@fapp0 (Functor_cat B (Product_cat C C)) (Functor_cat B C) (@comp_cat_cov_func B
  (Product_cat C C) C Prod) (@Struct_sigma (Functor B C) (λ _ : τ (Functor B C), Functor B C)
  (@kernel_adjunction_family_func B C (@additive_preadditive C Prod t A) t (@additive_terminal_object C Prod t A)
  P D) M)) (@cokernel_adjunction_family_func B C (@additive_preadditive C Prod t A) t T0 Q
  (@transf_arrow_diagram_func B C (@kernel_precomposition_family_func B C (@additive_preadditive C Prod t A) t
  (@additive_terminal_object C Prod t A) P M D p) (@kernel_adjunction_family_func B C (@additive_preadditive C
  Prod t A) t (@additive_terminal_object C Prod t A) P D) (@one_cat_kernel_precomposition_second_transf B C
  (@additive_preadditive C Prod t A) C1 t (@additive_terminal_object C Prod t A) T0 P M D p)))) (@comp_fapp0
  (Functor_cat B C) (@fapp0 (Functor_cat B (Product_cat C C)) (Functor_cat B C) (@comp_cat_cov_func B (Product_cat
  C C) C Prod) (@Struct_sigma (Functor B C) (λ _ : τ (Functor B C), Functor B C) (@kernel_adjunction_family_func B
  C (@additive_preadditive C Prod t A) t (@additive_terminal_object C Prod t A) P D) M)) (@diagram_family_at_func
  B WalkingArrow_cat C D walking_arrow_src) (@cokernel_adjunction_family_func B C (@additive_preadditive C Prod t
  A) t T0 Q (@transf_arrow_diagram_func B C (@kernel_precomposition_family_func B C (@additive_preadditive C Prod
  t A) t (@additive_terminal_object C Prod t A) P M D p) (@kernel_adjunction_family_func B C
  (@additive_preadditive C Prod t A) t (@additive_terminal_object C Prod t A) P D)
  (@one_cat_kernel_precomposition_second_transf B C (@additive_preadditive C Prod t A) C1 t
  (@additive_terminal_object C Prod t A) T0 P M D p))) (@one_cat_kernel_cover_cokernel_descent B C C1 Prod t
  A T0 P Q N M D p zp) (@one_cat_difference_cospan_transf B C C1 Prod t A T0 (@kernel_adjunction_family_func B C
  (@additive_preadditive C Prod t A) t (@additive_terminal_object C Prod t A) P D) M (@diagram_family_at_func B
  WalkingArrow_cat C D walking_arrow_src) (@kernel_adjunction_family_inclusion_transf B C (@additive_preadditive C
  Prod t A) t (@additive_terminal_object C Prod t A) P D) p)) (@one_cat_kernel_cover_cokernel_input B C C1
  Prod t A T0 P Q M D p))
≔ @one_cat_coimage_cover_descent_reconstruction B C (@additive_preadditive C Prod t A) C1 t
  (@additive_terminal_object C Prod t A) T0 P Q (@one_cat_kernel_difference_diagram B C C1 Prod t A T0 P M D
  p) (@one_cat_difference_cospan_zero_cokernel_cover B C C1 Prod t A T0 P Q N
  (@kernel_adjunction_family_func B C (@additive_preadditive C Prod t A) t (@additive_terminal_object C Prod t A)
  P D) M (@diagram_family_at_func B WalkingArrow_cat C D walking_arrow_src)
  (@kernel_adjunction_family_inclusion_transf B C (@additive_preadditive C Prod t A) t (@additive_terminal_object
  C Prod t A) P D) p zp) (@cokernel_adjunction_family_func B C (@additive_preadditive C Prod t A) t T0 Q
  (@transf_arrow_diagram_func B C (@kernel_precomposition_family_func B C (@additive_preadditive C Prod t A) t
  (@additive_terminal_object C Prod t A) P M D p) (@kernel_adjunction_family_func B C (@additive_preadditive C
  Prod t A) t (@additive_terminal_object C Prod t A) P D) (@one_cat_kernel_precomposition_second_transf B C
  (@additive_preadditive C Prod t A) C1 t (@additive_terminal_object C Prod t A) T0 P M D p)))
  (@one_cat_kernel_cover_cokernel_input B C C1 Prod t A T0 P Q M D p)
  (@one_cat_kernel_cover_cokernel_input_zero B C C1 Prod t A T0 P Q M D p);

// The second injection makes the descended map annihilate the original p.
symbol one_cat_kernel_cover_cokernel_descent_second_zero [B C : Cat] (C1 : τ (IsNCat (cat_succ cat_zero) C))
  [Prod : τ (Functor (Product_cat C C) C)] [t : τ (Obj C)] (A : τ (@AdditiveCategory C Prod t)) (T0 : τ
  (@TerminalObject (Op_cat C) t)) (P : τ (@KernelAdjunctionStructure C (@additive_preadditive C Prod t A) t
  (@additive_terminal_object C Prod t A))) (Q : τ (@CokernelAdjunctionStructure C (@additive_preadditive C Prod t
  A) t T0)) (N : τ (@OneCatAdjunctionNormality C (@additive_preadditive C Prod t A) C1 t
  (@additive_terminal_object C Prod t A) T0 P Q)) (M : τ (Functor B C)) (D : τ (Functor B (Functor_cat
  WalkingArrow_cat C))) (p : τ (@Transf B C M (@diagram_family_at_func B WalkingArrow_cat C D walking_arrow_src)))
  (zp : τ (@= (@Transf B C (@diagram_family_at_func B WalkingArrow_cat C D walking_arrow_src)
  (@cokernel_adjunction_family_func B C (@additive_preadditive C Prod t A) t T0 Q (@transf_arrow_diagram_func B C
  M (@diagram_family_at_func B WalkingArrow_cat C D walking_arrow_src) p)))
  (@cokernel_adjunction_family_projection_transf B C (@additive_preadditive C Prod t A) t T0 Q
  (@transf_arrow_diagram_func B C M (@diagram_family_at_func B WalkingArrow_cat C D walking_arrow_src) p))
  (@zero_arrow_family_zero_transf B C t (@additive_terminal_object C Prod t A) T0 (@diagram_family_at_func B
  WalkingArrow_cat C D walking_arrow_src) (@cokernel_adjunction_family_func B C (@additive_preadditive C Prod t A)
  t T0 Q (@transf_arrow_diagram_func B C M (@diagram_family_at_func B WalkingArrow_cat C D walking_arrow_src)
  p)))))
 : τ (@= (@Transf B C M (@cokernel_adjunction_family_func B C (@additive_preadditive C Prod t A) t T0 Q
  (@transf_arrow_diagram_func B C (@kernel_precomposition_family_func B C (@additive_preadditive C Prod t A) t
  (@additive_terminal_object C Prod t A) P M D p) (@kernel_adjunction_family_func B C (@additive_preadditive C
  Prod t A) t (@additive_terminal_object C Prod t A) P D) (@one_cat_kernel_precomposition_second_transf B C
  (@additive_preadditive C Prod t A) C1 t (@additive_terminal_object C Prod t A) T0 P M D p)))) (@comp_fapp0
  (Functor_cat B C) M (@diagram_family_at_func B WalkingArrow_cat C D walking_arrow_src)
  (@cokernel_adjunction_family_func B C (@additive_preadditive C Prod t A) t T0 Q (@transf_arrow_diagram_func B C
  (@kernel_precomposition_family_func B C (@additive_preadditive C Prod t A) t (@additive_terminal_object C Prod t
  A) P M D p) (@kernel_adjunction_family_func B C (@additive_preadditive C Prod t A) t (@additive_terminal_object
  C Prod t A) P D) (@one_cat_kernel_precomposition_second_transf B C (@additive_preadditive C Prod t A) C1 t
  (@additive_terminal_object C Prod t A) T0 P M D p))) (@one_cat_kernel_cover_cokernel_descent B C C1 Prod t
  A T0 P Q N M D p zp) p) (@zero_arrow_family_zero_transf B C t (@additive_terminal_object C Prod t A) T0 M
  (@cokernel_adjunction_family_func B C (@additive_preadditive C Prod t A) t T0 Q (@transf_arrow_diagram_func B C
  (@kernel_precomposition_family_func B C (@additive_preadditive C Prod t A) t (@additive_terminal_object C Prod t
  A) P M D p) (@kernel_adjunction_family_func B C (@additive_preadditive C Prod t A) t (@additive_terminal_object
  C Prod t A) P D) (@one_cat_kernel_precomposition_second_transf B C (@additive_preadditive C Prod t A) C1 t
  (@additive_terminal_object C Prod t A) T0 P M D p)))))
≔ @one_cat_difference_cospan_second_from_factor_path B C C1 Prod t A T0 (@kernel_adjunction_family_func B C
  (@additive_preadditive C Prod t A) t (@additive_terminal_object C Prod t A) P D) M (@diagram_family_at_func B
  WalkingArrow_cat C D walking_arrow_src) (@cokernel_adjunction_family_func B C (@additive_preadditive C Prod t A)
  t T0 Q (@transf_arrow_diagram_func B C (@kernel_precomposition_family_func B C (@additive_preadditive C Prod t
  A) t (@additive_terminal_object C Prod t A) P M D p) (@kernel_adjunction_family_func B C (@additive_preadditive
  C Prod t A) t (@additive_terminal_object C Prod t A) P D) (@one_cat_kernel_precomposition_second_transf B C
  (@additive_preadditive C Prod t A) C1 t (@additive_terminal_object C Prod t A) T0 P M D p)))
  (@kernel_adjunction_family_inclusion_transf B C (@additive_preadditive C Prod t A) t (@additive_terminal_object
  C Prod t A) P D) p (@one_cat_kernel_cover_cokernel_descent B C C1 Prod t A T0 P Q N M D p zp)
  (@cokernel_adjunction_family_projection_transf B C (@additive_preadditive C Prod t A) t T0 Q
  (@transf_arrow_diagram_func B C (@kernel_precomposition_family_func B C (@additive_preadditive C Prod t A) t
  (@additive_terminal_object C Prod t A) P M D p) (@kernel_adjunction_family_func B C (@additive_preadditive C
  Prod t A) t (@additive_terminal_object C Prod t A) P D) (@one_cat_kernel_precomposition_second_transf B C
  (@additive_preadditive C Prod t A) C1 t (@additive_terminal_object C Prod t A) T0 P M D p)))
  (@one_cat_kernel_cover_cokernel_descent_path B C C1 Prod t A T0 P Q N M D p zp);

// Cancellation of the original p forces the descended map to zero.
symbol one_cat_kernel_cover_cokernel_descent_zero [B C : Cat] (C1 : τ (IsNCat (cat_succ cat_zero) C)) [Prod
  : τ (Functor (Product_cat C C) C)] [t : τ (Obj C)] (A : τ (@AdditiveCategory C Prod t)) (T0 : τ (@TerminalObject
  (Op_cat C) t)) (P : τ (@KernelAdjunctionStructure C (@additive_preadditive C Prod t A) t
  (@additive_terminal_object C Prod t A))) (Q : τ (@CokernelAdjunctionStructure C (@additive_preadditive C Prod t
  A) t T0)) (N : τ (@OneCatAdjunctionNormality C (@additive_preadditive C Prod t A) C1 t
  (@additive_terminal_object C Prod t A) T0 P Q)) (M : τ (Functor B C)) (D : τ (Functor B (Functor_cat
  WalkingArrow_cat C))) (p : τ (@Transf B C M (@diagram_family_at_func B WalkingArrow_cat C D walking_arrow_src)))
  (zp : τ (@= (@Transf B C (@diagram_family_at_func B WalkingArrow_cat C D walking_arrow_src)
  (@cokernel_adjunction_family_func B C (@additive_preadditive C Prod t A) t T0 Q (@transf_arrow_diagram_func B C
  M (@diagram_family_at_func B WalkingArrow_cat C D walking_arrow_src) p)))
  (@cokernel_adjunction_family_projection_transf B C (@additive_preadditive C Prod t A) t T0 Q
  (@transf_arrow_diagram_func B C M (@diagram_family_at_func B WalkingArrow_cat C D walking_arrow_src) p))
  (@zero_arrow_family_zero_transf B C t (@additive_terminal_object C Prod t A) T0 (@diagram_family_at_func B
  WalkingArrow_cat C D walking_arrow_src) (@cokernel_adjunction_family_func B C (@additive_preadditive C Prod t A)
  t T0 Q (@transf_arrow_diagram_func B C M (@diagram_family_at_func B WalkingArrow_cat C D walking_arrow_src)
  p)))))
 : τ (@= (@Transf B C (@diagram_family_at_func B WalkingArrow_cat C D walking_arrow_src)
  (@cokernel_adjunction_family_func B C (@additive_preadditive C Prod t A) t T0 Q (@transf_arrow_diagram_func B C
  (@kernel_precomposition_family_func B C (@additive_preadditive C Prod t A) t (@additive_terminal_object C Prod t
  A) P M D p) (@kernel_adjunction_family_func B C (@additive_preadditive C Prod t A) t (@additive_terminal_object
  C Prod t A) P D) (@one_cat_kernel_precomposition_second_transf B C (@additive_preadditive C Prod t A) C1 t
  (@additive_terminal_object C Prod t A) T0 P M D p)))) (@one_cat_kernel_cover_cokernel_descent B C C1 Prod
  t A T0 P Q N M D p zp) (@zero_arrow_family_zero_transf B C t (@additive_terminal_object C Prod t A) T0
  (@diagram_family_at_func B WalkingArrow_cat C D walking_arrow_src) (@cokernel_adjunction_family_func B C
  (@additive_preadditive C Prod t A) t T0 Q (@transf_arrow_diagram_func B C (@kernel_precomposition_family_func B
  C (@additive_preadditive C Prod t A) t (@additive_terminal_object C Prod t A) P M D p)
  (@kernel_adjunction_family_func B C (@additive_preadditive C Prod t A) t (@additive_terminal_object C Prod t A)
  P D) (@one_cat_kernel_precomposition_second_transf B C (@additive_preadditive C Prod t A) C1 t
  (@additive_terminal_object C Prod t A) T0 P M D p)))))
≔ @one_cat_coimage_cover_reflect_path B C (@additive_preadditive C Prod t A) C1 t (@additive_terminal_object
  C Prod t A) T0 P Q (@transf_arrow_diagram_func B C M (@diagram_family_at_func B WalkingArrow_cat C D
  walking_arrow_src) p) (@one_cat_zero_cokernel_cover_omega B C (@additive_preadditive C Prod t A) C1 t
  (@additive_terminal_object C Prod t A) T0 P Q N (@transf_arrow_diagram_func B C M (@diagram_family_at_func B
  WalkingArrow_cat C D walking_arrow_src) p) zp) (@cokernel_adjunction_family_func B C (@additive_preadditive C
  Prod t A) t T0 Q (@transf_arrow_diagram_func B C (@kernel_precomposition_family_func B C (@additive_preadditive
  C Prod t A) t (@additive_terminal_object C Prod t A) P M D p) (@kernel_adjunction_family_func B C
  (@additive_preadditive C Prod t A) t (@additive_terminal_object C Prod t A) P D)
  (@one_cat_kernel_precomposition_second_transf B C (@additive_preadditive C Prod t A) C1 t
  (@additive_terminal_object C Prod t A) T0 P M D p))) (@one_cat_kernel_cover_cokernel_descent B C C1 Prod t
  A T0 P Q N M D p zp) (@zero_arrow_family_zero_transf B C t (@additive_terminal_object C Prod t A) T0
  (@diagram_family_at_func B WalkingArrow_cat C D walking_arrow_src) (@cokernel_adjunction_family_func B C
  (@additive_preadditive C Prod t A) t T0 Q (@transf_arrow_diagram_func B C (@kernel_precomposition_family_func B
  C (@additive_preadditive C Prod t A) t (@additive_terminal_object C Prod t A) P M D p)
  (@kernel_adjunction_family_func B C (@additive_preadditive C Prod t A) t (@additive_terminal_object C Prod t A)
  P D) (@one_cat_kernel_precomposition_second_transf B C (@additive_preadditive C Prod t A) C1 t
  (@additive_terminal_object C Prod t A) T0 P M D p)))) (@eq_trans _ _ _ _
  (@one_cat_kernel_cover_cokernel_descent_second_zero B C C1 Prod t A T0 P Q N M D p zp) (@eq_sym _ _ _
  (@one_cat_zero_family_precompose_path B C C1 t (@additive_terminal_object C Prod t A) T0 M
  (@diagram_family_at_func B WalkingArrow_cat C D walking_arrow_src) (@cokernel_adjunction_family_func B C
  (@additive_preadditive C Prod t A) t T0 Q (@transf_arrow_diagram_func B C (@kernel_precomposition_family_func B
  C (@additive_preadditive C Prod t A) t (@additive_terminal_object C Prod t A) P M D p)
  (@kernel_adjunction_family_func B C (@additive_preadditive C Prod t A) t (@additive_terminal_object C Prod t A)
  P D) (@one_cat_kernel_precomposition_second_transf B C (@additive_preadditive C Prod t A) C1 t
  (@additive_terminal_object C Prod t A) T0 P M D p))) p)));

// The first injection forces the original cokernel projection of r to zero.
symbol one_cat_kernel_precomposition_cokernel_zero [B C : Cat] (C1 : τ (IsNCat (cat_succ cat_zero) C)) [Prod
  : τ (Functor (Product_cat C C) C)] [t : τ (Obj C)] (A : τ (@AdditiveCategory C Prod t)) (T0 : τ (@TerminalObject
  (Op_cat C) t)) (P : τ (@KernelAdjunctionStructure C (@additive_preadditive C Prod t A) t
  (@additive_terminal_object C Prod t A))) (Q : τ (@CokernelAdjunctionStructure C (@additive_preadditive C Prod t
  A) t T0)) (N : τ (@OneCatAdjunctionNormality C (@additive_preadditive C Prod t A) C1 t
  (@additive_terminal_object C Prod t A) T0 P Q)) (M : τ (Functor B C)) (D : τ (Functor B (Functor_cat
  WalkingArrow_cat C))) (p : τ (@Transf B C M (@diagram_family_at_func B WalkingArrow_cat C D walking_arrow_src)))
  (zp : τ (@= (@Transf B C (@diagram_family_at_func B WalkingArrow_cat C D walking_arrow_src)
  (@cokernel_adjunction_family_func B C (@additive_preadditive C Prod t A) t T0 Q (@transf_arrow_diagram_func B C
  M (@diagram_family_at_func B WalkingArrow_cat C D walking_arrow_src) p)))
  (@cokernel_adjunction_family_projection_transf B C (@additive_preadditive C Prod t A) t T0 Q
  (@transf_arrow_diagram_func B C M (@diagram_family_at_func B WalkingArrow_cat C D walking_arrow_src) p))
  (@zero_arrow_family_zero_transf B C t (@additive_terminal_object C Prod t A) T0 (@diagram_family_at_func B
  WalkingArrow_cat C D walking_arrow_src) (@cokernel_adjunction_family_func B C (@additive_preadditive C Prod t A)
  t T0 Q (@transf_arrow_diagram_func B C M (@diagram_family_at_func B WalkingArrow_cat C D walking_arrow_src)
  p)))))
 : τ (@= (@Transf B C (@kernel_adjunction_family_func B C (@additive_preadditive C Prod t A) t
  (@additive_terminal_object C Prod t A) P D) (@cokernel_adjunction_family_func B C (@additive_preadditive C Prod
  t A) t T0 Q (@transf_arrow_diagram_func B C (@kernel_precomposition_family_func B C (@additive_preadditive C
  Prod t A) t (@additive_terminal_object C Prod t A) P M D p) (@kernel_adjunction_family_func B C
  (@additive_preadditive C Prod t A) t (@additive_terminal_object C Prod t A) P D)
  (@one_cat_kernel_precomposition_second_transf B C (@additive_preadditive C Prod t A) C1 t
  (@additive_terminal_object C Prod t A) T0 P M D p)))) (@cokernel_adjunction_family_projection_transf B C
  (@additive_preadditive C Prod t A) t T0 Q (@transf_arrow_diagram_func B C (@kernel_precomposition_family_func B
  C (@additive_preadditive C Prod t A) t (@additive_terminal_object C Prod t A) P M D p)
  (@kernel_adjunction_family_func B C (@additive_preadditive C Prod t A) t (@additive_terminal_object C Prod t A)
  P D) (@one_cat_kernel_precomposition_second_transf B C (@additive_preadditive C Prod t A) C1 t
  (@additive_terminal_object C Prod t A) T0 P M D p))) (@zero_arrow_family_zero_transf B C t
  (@additive_terminal_object C Prod t A) T0 (@kernel_adjunction_family_func B C (@additive_preadditive C Prod t A)
  t (@additive_terminal_object C Prod t A) P D) (@cokernel_adjunction_family_func B C (@additive_preadditive C
  Prod t A) t T0 Q (@transf_arrow_diagram_func B C (@kernel_precomposition_family_func B C (@additive_preadditive
  C Prod t A) t (@additive_terminal_object C Prod t A) P M D p) (@kernel_adjunction_family_func B C
  (@additive_preadditive C Prod t A) t (@additive_terminal_object C Prod t A) P D)
  (@one_cat_kernel_precomposition_second_transf B C (@additive_preadditive C Prod t A) C1 t
  (@additive_terminal_object C Prod t A) T0 P M D p)))))
≔ @one_cat_product_first_zero_reflect_path B C C1 Prod t A T0 (@kernel_adjunction_family_func B C
  (@additive_preadditive C Prod t A) t (@additive_terminal_object C Prod t A) P D) M
  (@cokernel_adjunction_family_func B C (@additive_preadditive C Prod t A) t T0 Q (@transf_arrow_diagram_func B C
  (@kernel_precomposition_family_func B C (@additive_preadditive C Prod t A) t (@additive_terminal_object C Prod t
  A) P M D p) (@kernel_adjunction_family_func B C (@additive_preadditive C Prod t A) t (@additive_terminal_object
  C Prod t A) P D) (@one_cat_kernel_precomposition_second_transf B C (@additive_preadditive C Prod t A) C1 t
  (@additive_terminal_object C Prod t A) T0 P M D p))) (@cokernel_adjunction_family_projection_transf B C
  (@additive_preadditive C Prod t A) t T0 Q (@transf_arrow_diagram_func B C (@kernel_precomposition_family_func B
  C (@additive_preadditive C Prod t A) t (@additive_terminal_object C Prod t A) P M D p)
  (@kernel_adjunction_family_func B C (@additive_preadditive C Prod t A) t (@additive_terminal_object C Prod t A)
  P D) (@one_cat_kernel_precomposition_second_transf B C (@additive_preadditive C Prod t A) C1 t
  (@additive_terminal_object C Prod t A) T0 P M D p))) (@eq_trans _ _ _ _ (@eq_sym _ _ _
  (@one_cat_kernel_cover_cokernel_descent_path B C C1 Prod t A T0 P Q N M D p zp)) (@eq_trans _ _ _ _
  (@eq_ap (@Transf B C (@diagram_family_at_func B WalkingArrow_cat C D walking_arrow_src)
  (@cokernel_adjunction_family_func B C (@additive_preadditive C Prod t A) t T0 Q (@transf_arrow_diagram_func B C
  (@kernel_precomposition_family_func B C (@additive_preadditive C Prod t A) t (@additive_terminal_object C Prod t
  A) P M D p) (@kernel_adjunction_family_func B C (@additive_preadditive C Prod t A) t (@additive_terminal_object
  C Prod t A) P D) (@one_cat_kernel_precomposition_second_transf B C (@additive_preadditive C Prod t A) C1 t
  (@additive_terminal_object C Prod t A) T0 P M D p)))) (@Transf B C (@fapp0 (Functor_cat B (Product_cat C C))
  (Functor_cat B C) (@comp_cat_cov_func B (Product_cat C C) C Prod) (@Struct_sigma (Functor B C) (λ _ : τ (Functor
  B C), Functor B C) (@kernel_adjunction_family_func B C (@additive_preadditive C Prod t A) t
  (@additive_terminal_object C Prod t A) P D) M)) (@cokernel_adjunction_family_func B C (@additive_preadditive C
  Prod t A) t T0 Q (@transf_arrow_diagram_func B C (@kernel_precomposition_family_func B C (@additive_preadditive
  C Prod t A) t (@additive_terminal_object C Prod t A) P M D p) (@kernel_adjunction_family_func B C
  (@additive_preadditive C Prod t A) t (@additive_terminal_object C Prod t A) P D)
  (@one_cat_kernel_precomposition_second_transf B C (@additive_preadditive C Prod t A) C1 t
  (@additive_terminal_object C Prod t A) T0 P M D p)))) (λ a : τ (@Transf B C (@diagram_family_at_func B
  WalkingArrow_cat C D walking_arrow_src) (@cokernel_adjunction_family_func B C (@additive_preadditive C Prod t A)
  t T0 Q (@transf_arrow_diagram_func B C (@kernel_precomposition_family_func B C (@additive_preadditive C Prod t
  A) t (@additive_terminal_object C Prod t A) P M D p) (@kernel_adjunction_family_func B C (@additive_preadditive
  C Prod t A) t (@additive_terminal_object C Prod t A) P D) (@one_cat_kernel_precomposition_second_transf B C
  (@additive_preadditive C Prod t A) C1 t (@additive_terminal_object C Prod t A) T0 P M D p)))), (@comp_fapp0
  (Functor_cat B C) (@fapp0 (Functor_cat B (Product_cat C C)) (Functor_cat B C) (@comp_cat_cov_func B (Product_cat
  C C) C Prod) (@Struct_sigma (Functor B C) (λ _ : τ (Functor B C), Functor B C) (@kernel_adjunction_family_func B
  C (@additive_preadditive C Prod t A) t (@additive_terminal_object C Prod t A) P D) M)) (@diagram_family_at_func
  B WalkingArrow_cat C D walking_arrow_src) (@cokernel_adjunction_family_func B C (@additive_preadditive C Prod t
  A) t T0 Q (@transf_arrow_diagram_func B C (@kernel_precomposition_family_func B C (@additive_preadditive C Prod
  t A) t (@additive_terminal_object C Prod t A) P M D p) (@kernel_adjunction_family_func B C
  (@additive_preadditive C Prod t A) t (@additive_terminal_object C Prod t A) P D)
  (@one_cat_kernel_precomposition_second_transf B C (@additive_preadditive C Prod t A) C1 t
  (@additive_terminal_object C Prod t A) T0 P M D p))) a (@one_cat_difference_cospan_transf B C C1 Prod t A T0
  (@kernel_adjunction_family_func B C (@additive_preadditive C Prod t A) t (@additive_terminal_object C Prod t A)
  P D) M (@diagram_family_at_func B WalkingArrow_cat C D walking_arrow_src)
  (@kernel_adjunction_family_inclusion_transf B C (@additive_preadditive C Prod t A) t (@additive_terminal_object
  C Prod t A) P D) p))) (@one_cat_kernel_cover_cokernel_descent B C C1 Prod t A T0 P Q N M D p zp)
  (@zero_arrow_family_zero_transf B C t (@additive_terminal_object C Prod t A) T0 (@diagram_family_at_func B
  WalkingArrow_cat C D walking_arrow_src) (@cokernel_adjunction_family_func B C (@additive_preadditive C Prod t A)
  t T0 Q (@transf_arrow_diagram_func B C (@kernel_precomposition_family_func B C (@additive_preadditive C Prod t
  A) t (@additive_terminal_object C Prod t A) P M D p) (@kernel_adjunction_family_func B C (@additive_preadditive
  C Prod t A) t (@additive_terminal_object C Prod t A) P D) (@one_cat_kernel_precomposition_second_transf B C
  (@additive_preadditive C Prod t A) C1 t (@additive_terminal_object C Prod t A) T0 P M D p))))
  (@one_cat_kernel_cover_cokernel_descent_zero B C C1 Prod t A T0 P Q N M D p zp))
  (@one_cat_zero_family_precompose_path B C C1 t (@additive_terminal_object C Prod t A) T0 (@fapp0 (Functor_cat B
  (Product_cat C C)) (Functor_cat B C) (@comp_cat_cov_func B (Product_cat C C) C Prod) (@Struct_sigma (Functor B
  C) (λ _ : τ (Functor B C), Functor B C) (@kernel_adjunction_family_func B C (@additive_preadditive C Prod t A) t
  (@additive_terminal_object C Prod t A) P D) M)) (@diagram_family_at_func B WalkingArrow_cat C D
  walking_arrow_src) (@cokernel_adjunction_family_func B C (@additive_preadditive C Prod t A) t T0 Q
  (@transf_arrow_diagram_func B C (@kernel_precomposition_family_func B C (@additive_preadditive C Prod t A) t
  (@additive_terminal_object C Prod t A) P M D p) (@kernel_adjunction_family_func B C (@additive_preadditive C
  Prod t A) t (@additive_terminal_object C Prod t A) P D) (@one_cat_kernel_precomposition_second_transf B C
  (@additive_preadditive C Prod t A) C1 t (@additive_terminal_object C Prod t A) T0 P M D p)))
  (@one_cat_difference_cospan_transf B C C1 Prod t A T0 (@kernel_adjunction_family_func B C (@additive_preadditive
  C Prod t A) t (@additive_terminal_object C Prod t A) P D) M (@diagram_family_at_func B WalkingArrow_cat C D
  walking_arrow_src) (@kernel_adjunction_family_inclusion_transf B C (@additive_preadditive C Prod t A) t
  (@additive_terminal_object C Prod t A) P D) p))));

// Original normality turns that zero-cokernel proof into the actual categorical cover of r.
symbol one_cat_kernel_precomposition_cover_omega [B C : Cat] (C1 : τ (IsNCat (cat_succ cat_zero) C)) [Prod :
  τ (Functor (Product_cat C C) C)] [t : τ (Obj C)] (A : τ (@AdditiveCategory C Prod t)) (T0 : τ (@TerminalObject
  (Op_cat C) t)) (P : τ (@KernelAdjunctionStructure C (@additive_preadditive C Prod t A) t
  (@additive_terminal_object C Prod t A))) (Q : τ (@CokernelAdjunctionStructure C (@additive_preadditive C Prod t
  A) t T0)) (N : τ (@OneCatAdjunctionNormality C (@additive_preadditive C Prod t A) C1 t
  (@additive_terminal_object C Prod t A) T0 P Q)) (M : τ (Functor B C)) (D : τ (Functor B (Functor_cat
  WalkingArrow_cat C))) (p : τ (@Transf B C M (@diagram_family_at_func B WalkingArrow_cat C D walking_arrow_src)))
  (zp : τ (@= (@Transf B C (@diagram_family_at_func B WalkingArrow_cat C D walking_arrow_src)
  (@cokernel_adjunction_family_func B C (@additive_preadditive C Prod t A) t T0 Q (@transf_arrow_diagram_func B C
  M (@diagram_family_at_func B WalkingArrow_cat C D walking_arrow_src) p)))
  (@cokernel_adjunction_family_projection_transf B C (@additive_preadditive C Prod t A) t T0 Q
  (@transf_arrow_diagram_func B C M (@diagram_family_at_func B WalkingArrow_cat C D walking_arrow_src) p))
  (@zero_arrow_family_zero_transf B C t (@additive_terminal_object C Prod t A) T0 (@diagram_family_at_func B
  WalkingArrow_cat C D walking_arrow_src) (@cokernel_adjunction_family_func B C (@additive_preadditive C Prod t A)
  t T0 Q (@transf_arrow_diagram_func B C M (@diagram_family_at_func B WalkingArrow_cat C D walking_arrow_src)
  p)))))
 : τ (@OmegaEquivAlong (Functor_cat B C) (@comp_cat_fapp0 B (Functor_cat WalkingArrow_cat C) C
  (@adjunction_coimage_func C (@additive_preadditive C Prod t A) t (@additive_terminal_object C Prod t A) T0 P Q)
  (@transf_arrow_diagram_func B C (@kernel_precomposition_family_func B C (@additive_preadditive C Prod t A) t
  (@additive_terminal_object C Prod t A) P M D p) (@kernel_adjunction_family_func B C (@additive_preadditive C
  Prod t A) t (@additive_terminal_object C Prod t A) P D) (@one_cat_kernel_precomposition_second_transf B C
  (@additive_preadditive C Prod t A) C1 t (@additive_terminal_object C Prod t A) T0 P M D p)))
  (@kernel_adjunction_family_func B C (@additive_preadditive C Prod t A) t (@additive_terminal_object C Prod t A)
  P D) (@fapp0 _ _ (@comp_cat_con_fapp1_func B (Functor_cat WalkingArrow_cat C) C (@transf_arrow_diagram_func B C
  (@kernel_precomposition_family_func B C (@additive_preadditive C Prod t A) t (@additive_terminal_object C Prod t
  A) P M D p) (@kernel_adjunction_family_func B C (@additive_preadditive C Prod t A) t (@additive_terminal_object
  C Prod t A) P D) (@one_cat_kernel_precomposition_second_transf B C (@additive_preadditive C Prod t A) C1 t
  (@additive_terminal_object C Prod t A) T0 P M D p)) (@adjunction_coimage_func C (@additive_preadditive C Prod t
  A) t (@additive_terminal_object C Prod t A) T0 P Q) (@diagram_evaluation_at_func WalkingArrow_cat C
  walking_arrow_tgt)) (@one_cat_adjunction_coimage_to_target C (@additive_preadditive C Prod t A) C1 t
  (@additive_terminal_object C Prod t A) T0 P Q)))
≔ @one_cat_zero_cokernel_cover_omega B C (@additive_preadditive C Prod t A) C1 t (@additive_terminal_object C Prod
  t A) T0 P Q N (@transf_arrow_diagram_func B C (@kernel_precomposition_family_func B C (@additive_preadditive C
  Prod t A) t (@additive_terminal_object C Prod t A) P M D p) (@kernel_adjunction_family_func B C
  (@additive_preadditive C Prod t A) t (@additive_terminal_object C Prod t A) P D)
  (@one_cat_kernel_precomposition_second_transf B C (@additive_preadditive C Prod t A) C1 t
  (@additive_terminal_object C Prod t A) T0 P M D p)) (@one_cat_kernel_precomposition_cokernel_zero B C C1
  Prod t A T0 P Q N M D p zp);

// The derived categorical cover cancels the existing r as a whole map.
symbol one_cat_kernel_precomposition_reflect_path [B C : Cat] (C1 : τ (IsNCat (cat_succ cat_zero) C)) [Prod
  : τ (Functor (Product_cat C C) C)] [t : τ (Obj C)] (A : τ (@AdditiveCategory C Prod t)) (T0 : τ (@TerminalObject
  (Op_cat C) t)) (P : τ (@KernelAdjunctionStructure C (@additive_preadditive C Prod t A) t
  (@additive_terminal_object C Prod t A))) (Q : τ (@CokernelAdjunctionStructure C (@additive_preadditive C Prod t
  A) t T0)) (N : τ (@OneCatAdjunctionNormality C (@additive_preadditive C Prod t A) C1 t
  (@additive_terminal_object C Prod t A) T0 P Q)) (M : τ (Functor B C)) (D : τ (Functor B (Functor_cat
  WalkingArrow_cat C))) (p : τ (@Transf B C M (@diagram_family_at_func B WalkingArrow_cat C D walking_arrow_src)))
  (zp : τ (@= (@Transf B C (@diagram_family_at_func B WalkingArrow_cat C D walking_arrow_src)
  (@cokernel_adjunction_family_func B C (@additive_preadditive C Prod t A) t T0 Q (@transf_arrow_diagram_func B C
  M (@diagram_family_at_func B WalkingArrow_cat C D walking_arrow_src) p)))
  (@cokernel_adjunction_family_projection_transf B C (@additive_preadditive C Prod t A) t T0 Q
  (@transf_arrow_diagram_func B C M (@diagram_family_at_func B WalkingArrow_cat C D walking_arrow_src) p))
  (@zero_arrow_family_zero_transf B C t (@additive_terminal_object C Prod t A) T0 (@diagram_family_at_func B
  WalkingArrow_cat C D walking_arrow_src) (@cokernel_adjunction_family_func B C (@additive_preadditive C Prod t A)
  t T0 Q (@transf_arrow_diagram_func B C M (@diagram_family_at_func B WalkingArrow_cat C D walking_arrow_src)
  p))))) (V : τ (Functor B C)) (a b : τ (@Transf B C (@kernel_adjunction_family_func B C (@additive_preadditive C
  Prod t A) t (@additive_terminal_object C Prod t A) P D) V)) (e : τ (@= (@Transf B C
  (@kernel_precomposition_family_func B C (@additive_preadditive C Prod t A) t (@additive_terminal_object C Prod t
  A) P M D p) V) (@comp_fapp0 (Functor_cat B C) (@kernel_precomposition_family_func B C (@additive_preadditive C
  Prod t A) t (@additive_terminal_object C Prod t A) P M D p) (@kernel_adjunction_family_func B C
  (@additive_preadditive C Prod t A) t (@additive_terminal_object C Prod t A) P D) V a
  (@one_cat_kernel_precomposition_second_transf B C (@additive_preadditive C Prod t A) C1 t
  (@additive_terminal_object C Prod t A) T0 P M D p)) (@comp_fapp0 (Functor_cat B C)
  (@kernel_precomposition_family_func B C (@additive_preadditive C Prod t A) t (@additive_terminal_object C Prod t
  A) P M D p) (@kernel_adjunction_family_func B C (@additive_preadditive C Prod t A) t (@additive_terminal_object
  C Prod t A) P D) V b (@one_cat_kernel_precomposition_second_transf B C (@additive_preadditive C Prod t A) C1 t
  (@additive_terminal_object C Prod t A) T0 P M D p))))
 : τ (@= (@Transf B C (@kernel_adjunction_family_func B C (@additive_preadditive C Prod t A) t
  (@additive_terminal_object C Prod t A) P D) V) a b)
≔ @one_cat_coimage_cover_reflect_path B C (@additive_preadditive C Prod t A) C1 t (@additive_terminal_object
  C Prod t A) T0 P Q (@transf_arrow_diagram_func B C (@kernel_precomposition_family_func B C
  (@additive_preadditive C Prod t A) t (@additive_terminal_object C Prod t A) P M D p)
  (@kernel_adjunction_family_func B C (@additive_preadditive C Prod t A) t (@additive_terminal_object C Prod t A)
  P D) (@one_cat_kernel_precomposition_second_transf B C (@additive_preadditive C Prod t A) C1 t
  (@additive_terminal_object C Prod t A) T0 P M D p)) (@one_cat_kernel_precomposition_cover_omega B C C1
  Prod t A T0 P Q N M D p zp) V a b e;
