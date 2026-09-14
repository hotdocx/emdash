/* Whole difference-kernel covers, derived from the original K/Q and normality. */
require open emdash.emdash3_2_one_cat_difference_cover_closure;
require open emdash.emdash3_2_one_cat_difference_factor_paths;
require open emdash.emdash3_2_one_cat_kernel_family_restriction_paths;

// The original difference kernel is the whole cospan parameter object.
symbol one_cat_cospan_kernel_func [B C : Cat] (C1 : τ (IsNCat (cat_succ cat_zero) C)) [Prod : τ (Functor
  (Product_cat C C) C)] [t : τ (Obj C)] (A : τ (@AdditiveCategory C Prod t)) (T0 : τ (@TerminalObject (Op_cat C)
  t)) (P : τ (@KernelAdjunctionStructure C (@additive_preadditive C Prod t A) t (@additive_terminal_object C Prod
  t A))) (Q : τ (@CokernelAdjunctionStructure C (@additive_preadditive C Prod t A) t T0)) (X Y Z : τ (Functor B
  C)) (f : τ (@Transf B C X Z)) (g : τ (@Transf B C Y Z))
 : τ (Functor B C)
≔ (@kernel_adjunction_family_func B C (@additive_preadditive C Prod t A) t (@additive_terminal_object C Prod t A)
  P (@transf_arrow_diagram_func B C (@fapp0 (Functor_cat B (Product_cat C C)) (Functor_cat B C)
  (@comp_cat_cov_func B (Product_cat C C) C Prod) (@Struct_sigma (Functor B C) (λ _ : τ (Functor B C), Functor B
  C) X Y)) Z (@one_cat_difference_cospan_transf B C C1 Prod t A T0 X Y Z f g)));

// The original difference kernel projects to the original first object.
symbol one_cat_cospan_kernel_first [B C : Cat] (C1 : τ (IsNCat (cat_succ cat_zero) C)) [Prod : τ (Functor
  (Product_cat C C) C)] [t : τ (Obj C)] (A : τ (@AdditiveCategory C Prod t)) (T0 : τ (@TerminalObject (Op_cat C)
  t)) (P : τ (@KernelAdjunctionStructure C (@additive_preadditive C Prod t A) t (@additive_terminal_object C Prod
  t A))) (Q : τ (@CokernelAdjunctionStructure C (@additive_preadditive C Prod t A) t T0)) (X Y Z : τ (Functor B
  C)) (f : τ (@Transf B C X Z)) (g : τ (@Transf B C Y Z))
 : τ (@Transf B C (@kernel_adjunction_family_func B C (@additive_preadditive C Prod t A) t
  (@additive_terminal_object C Prod t A) P (@transf_arrow_diagram_func B C (@fapp0 (Functor_cat B (Product_cat C
  C)) (Functor_cat B C) (@comp_cat_cov_func B (Product_cat C C) C Prod) (@Struct_sigma (Functor B C) (λ _ : τ
  (Functor B C), Functor B C) X Y)) Z (@one_cat_difference_cospan_transf B C C1 Prod t A T0 X Y Z f g))) X)
≔ (@comp_fapp0 (Functor_cat B C) (@kernel_adjunction_family_func B C (@additive_preadditive C Prod t A) t
  (@additive_terminal_object C Prod t A) P (@transf_arrow_diagram_func B C (@fapp0 (Functor_cat B (Product_cat C
  C)) (Functor_cat B C) (@comp_cat_cov_func B (Product_cat C C) C Prod) (@Struct_sigma (Functor B C) (λ _ : τ
  (Functor B C), Functor B C) X Y)) Z (@one_cat_difference_cospan_transf B C C1 Prod t A T0 X Y Z f g))) (@fapp0
  (Functor_cat B (Product_cat C C)) (Functor_cat B C) (@comp_cat_cov_func B (Product_cat C C) C Prod)
  (@Struct_sigma (Functor B C) (λ _ : τ (Functor B C), Functor B C) X Y)) X (@one_cat_product_family_proj1 B C C1
  Prod (@additive_binary_products C Prod t A) X Y) (@kernel_adjunction_family_inclusion_transf B C
  (@additive_preadditive C Prod t A) t (@additive_terminal_object C Prod t A) P (@transf_arrow_diagram_func B C
  (@fapp0 (Functor_cat B (Product_cat C C)) (Functor_cat B C) (@comp_cat_cov_func B (Product_cat C C) C Prod)
  (@Struct_sigma (Functor B C) (λ _ : τ (Functor B C), Functor B C) X Y)) Z (@one_cat_difference_cospan_transf B C
  C1 Prod t A T0 X Y Z f g))));

// The same original difference kernel projects to the original second object.
symbol one_cat_cospan_kernel_second [B C : Cat] (C1 : τ (IsNCat (cat_succ cat_zero) C)) [Prod : τ (Functor
  (Product_cat C C) C)] [t : τ (Obj C)] (A : τ (@AdditiveCategory C Prod t)) (T0 : τ (@TerminalObject (Op_cat C)
  t)) (P : τ (@KernelAdjunctionStructure C (@additive_preadditive C Prod t A) t (@additive_terminal_object C Prod
  t A))) (Q : τ (@CokernelAdjunctionStructure C (@additive_preadditive C Prod t A) t T0)) (X Y Z : τ (Functor B
  C)) (f : τ (@Transf B C X Z)) (g : τ (@Transf B C Y Z))
 : τ (@Transf B C (@kernel_adjunction_family_func B C (@additive_preadditive C Prod t A) t
  (@additive_terminal_object C Prod t A) P (@transf_arrow_diagram_func B C (@fapp0 (Functor_cat B (Product_cat C
  C)) (Functor_cat B C) (@comp_cat_cov_func B (Product_cat C C) C Prod) (@Struct_sigma (Functor B C) (λ _ : τ
  (Functor B C), Functor B C) X Y)) Z (@one_cat_difference_cospan_transf B C C1 Prod t A T0 X Y Z f g))) Y)
≔ (@comp_fapp0 (Functor_cat B C) (@kernel_adjunction_family_func B C (@additive_preadditive C Prod t A) t
  (@additive_terminal_object C Prod t A) P (@transf_arrow_diagram_func B C (@fapp0 (Functor_cat B (Product_cat C
  C)) (Functor_cat B C) (@comp_cat_cov_func B (Product_cat C C) C Prod) (@Struct_sigma (Functor B C) (λ _ : τ
  (Functor B C), Functor B C) X Y)) Z (@one_cat_difference_cospan_transf B C C1 Prod t A T0 X Y Z f g))) (@fapp0
  (Functor_cat B (Product_cat C C)) (Functor_cat B C) (@comp_cat_cov_func B (Product_cat C C) C Prod)
  (@Struct_sigma (Functor B C) (λ _ : τ (Functor B C), Functor B C) X Y)) Y (@one_cat_product_family_proj2 B C C1
  Prod (@additive_binary_products C Prod t A) X Y) (@kernel_adjunction_family_inclusion_transf B C
  (@additive_preadditive C Prod t A) t (@additive_terminal_object C Prod t A) P (@transf_arrow_diagram_func B C
  (@fapp0 (Functor_cat B (Product_cat C C)) (Functor_cat B C) (@comp_cat_cov_func B (Product_cat C C) C Prod)
  (@Struct_sigma (Functor B C) (λ _ : τ (Functor B C), Functor B C) X Y)) Z (@one_cat_difference_cospan_transf B C
  C1 Prod t A T0 X Y Z f g))));

// The original two projections satisfy the whole cospan relation by zero-difference reflection.
symbol one_cat_cospan_kernel_compatibility [B C : Cat] (C1 : τ (IsNCat (cat_succ cat_zero) C)) [Prod : τ
  (Functor (Product_cat C C) C)] [t : τ (Obj C)] (A : τ (@AdditiveCategory C Prod t)) (T0 : τ (@TerminalObject
  (Op_cat C) t)) (P : τ (@KernelAdjunctionStructure C (@additive_preadditive C Prod t A) t
  (@additive_terminal_object C Prod t A))) (Q : τ (@CokernelAdjunctionStructure C (@additive_preadditive C Prod t
  A) t T0)) (X Y Z : τ (Functor B C)) (f : τ (@Transf B C X Z)) (g : τ (@Transf B C Y Z))
 : τ (@= (@Transf B C (@kernel_adjunction_family_func B C (@additive_preadditive C Prod t A) t
  (@additive_terminal_object C Prod t A) P (@transf_arrow_diagram_func B C (@fapp0 (Functor_cat B (Product_cat C
  C)) (Functor_cat B C) (@comp_cat_cov_func B (Product_cat C C) C Prod) (@Struct_sigma (Functor B C) (λ _ : τ
  (Functor B C), Functor B C) X Y)) Z (@one_cat_difference_cospan_transf B C C1 Prod t A T0 X Y Z f g))) Z)
  (@comp_fapp0 (Functor_cat B C) (@kernel_adjunction_family_func B C (@additive_preadditive C Prod t A) t
  (@additive_terminal_object C Prod t A) P (@transf_arrow_diagram_func B C (@fapp0 (Functor_cat B (Product_cat C
  C)) (Functor_cat B C) (@comp_cat_cov_func B (Product_cat C C) C Prod) (@Struct_sigma (Functor B C) (λ _ : τ
  (Functor B C), Functor B C) X Y)) Z (@one_cat_difference_cospan_transf B C C1 Prod t A T0 X Y Z f g))) X Z f
  (@one_cat_cospan_kernel_first B C C1 Prod t A T0 P Q X Y Z f g)) (@comp_fapp0 (Functor_cat B C)
  (@kernel_adjunction_family_func B C (@additive_preadditive C Prod t A) t (@additive_terminal_object C Prod t A)
  P (@transf_arrow_diagram_func B C (@fapp0 (Functor_cat B (Product_cat C C)) (Functor_cat B C)
  (@comp_cat_cov_func B (Product_cat C C) C Prod) (@Struct_sigma (Functor B C) (λ _ : τ (Functor B C), Functor B
  C) X Y)) Z (@one_cat_difference_cospan_transf B C C1 Prod t A T0 X Y Z f g))) Y Z g
  (@one_cat_cospan_kernel_second B C C1 Prod t A T0 P Q X Y Z f g)))
≔ (@eq_trans _ _ _ _ (@comp_assoc (Functor_cat B C) (@kernel_adjunction_family_func B C (@additive_preadditive C
  Prod t A) t (@additive_terminal_object C Prod t A) P (@transf_arrow_diagram_func B C (@fapp0 (Functor_cat B
  (Product_cat C C)) (Functor_cat B C) (@comp_cat_cov_func B (Product_cat C C) C Prod) (@Struct_sigma (Functor B
  C) (λ _ : τ (Functor B C), Functor B C) X Y)) Z (@one_cat_difference_cospan_transf B C C1 Prod t A T0 X Y Z f
  g))) (@fapp0 (Functor_cat B (Product_cat C C)) (Functor_cat B C) (@comp_cat_cov_func B (Product_cat C C) C Prod)
  (@Struct_sigma (Functor B C) (λ _ : τ (Functor B C), Functor B C) X Y)) X Z f (@one_cat_product_family_proj1 B C
  C1 Prod (@additive_binary_products C Prod t A) X Y) (@kernel_adjunction_family_inclusion_transf B C
  (@additive_preadditive C Prod t A) t (@additive_terminal_object C Prod t A) P (@transf_arrow_diagram_func B C
  (@fapp0 (Functor_cat B (Product_cat C C)) (Functor_cat B C) (@comp_cat_cov_func B (Product_cat C C) C Prod)
  (@Struct_sigma (Functor B C) (λ _ : τ (Functor B C), Functor B C) X Y)) Z (@one_cat_difference_cospan_transf B C
  C1 Prod t A T0 X Y Z f g)))) (@eq_trans _ _ _ _ (@one_cat_difference_family_zero_reflect B C C1 Prod t A T0
  (@kernel_adjunction_family_func B C (@additive_preadditive C Prod t A) t (@additive_terminal_object C Prod t A)
  P (@transf_arrow_diagram_func B C (@fapp0 (Functor_cat B (Product_cat C C)) (Functor_cat B C)
  (@comp_cat_cov_func B (Product_cat C C) C Prod) (@Struct_sigma (Functor B C) (λ _ : τ (Functor B C), Functor B
  C) X Y)) Z (@one_cat_difference_cospan_transf B C C1 Prod t A T0 X Y Z f g))) Z (@comp_fapp0 (Functor_cat B C)
  (@kernel_adjunction_family_func B C (@additive_preadditive C Prod t A) t (@additive_terminal_object C Prod t A)
  P (@transf_arrow_diagram_func B C (@fapp0 (Functor_cat B (Product_cat C C)) (Functor_cat B C)
  (@comp_cat_cov_func B (Product_cat C C) C Prod) (@Struct_sigma (Functor B C) (λ _ : τ (Functor B C), Functor B
  C) X Y)) Z (@one_cat_difference_cospan_transf B C C1 Prod t A T0 X Y Z f g))) (@fapp0 (Functor_cat B
  (Product_cat C C)) (Functor_cat B C) (@comp_cat_cov_func B (Product_cat C C) C Prod) (@Struct_sigma (Functor B
  C) (λ _ : τ (Functor B C), Functor B C) X Y)) Z (@comp_fapp0 (Functor_cat B C) (@fapp0 (Functor_cat B
  (Product_cat C C)) (Functor_cat B C) (@comp_cat_cov_func B (Product_cat C C) C Prod) (@Struct_sigma (Functor B
  C) (λ _ : τ (Functor B C), Functor B C) X Y)) X Z f (@one_cat_product_family_proj1 B C C1 Prod
  (@additive_binary_products C Prod t A) X Y)) (@kernel_adjunction_family_inclusion_transf B C
  (@additive_preadditive C Prod t A) t (@additive_terminal_object C Prod t A) P (@transf_arrow_diagram_func B C
  (@fapp0 (Functor_cat B (Product_cat C C)) (Functor_cat B C) (@comp_cat_cov_func B (Product_cat C C) C Prod)
  (@Struct_sigma (Functor B C) (λ _ : τ (Functor B C), Functor B C) X Y)) Z (@one_cat_difference_cospan_transf B C
  C1 Prod t A T0 X Y Z f g)))) (@comp_fapp0 (Functor_cat B C) (@kernel_adjunction_family_func B C
  (@additive_preadditive C Prod t A) t (@additive_terminal_object C Prod t A) P (@transf_arrow_diagram_func B C
  (@fapp0 (Functor_cat B (Product_cat C C)) (Functor_cat B C) (@comp_cat_cov_func B (Product_cat C C) C Prod)
  (@Struct_sigma (Functor B C) (λ _ : τ (Functor B C), Functor B C) X Y)) Z (@one_cat_difference_cospan_transf B C
  C1 Prod t A T0 X Y Z f g))) (@fapp0 (Functor_cat B (Product_cat C C)) (Functor_cat B C) (@comp_cat_cov_func B
  (Product_cat C C) C Prod) (@Struct_sigma (Functor B C) (λ _ : τ (Functor B C), Functor B C) X Y)) Z (@comp_fapp0
  (Functor_cat B C) (@fapp0 (Functor_cat B (Product_cat C C)) (Functor_cat B C) (@comp_cat_cov_func B (Product_cat
  C C) C Prod) (@Struct_sigma (Functor B C) (λ _ : τ (Functor B C), Functor B C) X Y)) Y Z g
  (@one_cat_product_family_proj2 B C C1 Prod (@additive_binary_products C Prod t A) X Y))
  (@kernel_adjunction_family_inclusion_transf B C (@additive_preadditive C Prod t A) t (@additive_terminal_object
  C Prod t A) P (@transf_arrow_diagram_func B C (@fapp0 (Functor_cat B (Product_cat C C)) (Functor_cat B C)
  (@comp_cat_cov_func B (Product_cat C C) C Prod) (@Struct_sigma (Functor B C) (λ _ : τ (Functor B C), Functor B
  C) X Y)) Z (@one_cat_difference_cospan_transf B C C1 Prod t A T0 X Y Z f g)))) (@eq_trans _ _ _ _ (@eq_sym _ _ _
  (@one_cat_difference_family_precompose_path B C C1 Prod t A T0 (@kernel_adjunction_family_func B C
  (@additive_preadditive C Prod t A) t (@additive_terminal_object C Prod t A) P (@transf_arrow_diagram_func B C
  (@fapp0 (Functor_cat B (Product_cat C C)) (Functor_cat B C) (@comp_cat_cov_func B (Product_cat C C) C Prod)
  (@Struct_sigma (Functor B C) (λ _ : τ (Functor B C), Functor B C) X Y)) Z (@one_cat_difference_cospan_transf B C
  C1 Prod t A T0 X Y Z f g))) (@fapp0 (Functor_cat B (Product_cat C C)) (Functor_cat B C) (@comp_cat_cov_func B
  (Product_cat C C) C Prod) (@Struct_sigma (Functor B C) (λ _ : τ (Functor B C), Functor B C) X Y)) Z (@comp_fapp0
  (Functor_cat B C) (@fapp0 (Functor_cat B (Product_cat C C)) (Functor_cat B C) (@comp_cat_cov_func B (Product_cat
  C C) C Prod) (@Struct_sigma (Functor B C) (λ _ : τ (Functor B C), Functor B C) X Y)) X Z f
  (@one_cat_product_family_proj1 B C C1 Prod (@additive_binary_products C Prod t A) X Y)) (@comp_fapp0
  (Functor_cat B C) (@fapp0 (Functor_cat B (Product_cat C C)) (Functor_cat B C) (@comp_cat_cov_func B (Product_cat
  C C) C Prod) (@Struct_sigma (Functor B C) (λ _ : τ (Functor B C), Functor B C) X Y)) Y Z g
  (@one_cat_product_family_proj2 B C C1 Prod (@additive_binary_products C Prod t A) X Y))
  (@kernel_adjunction_family_inclusion_transf B C (@additive_preadditive C Prod t A) t (@additive_terminal_object
  C Prod t A) P (@transf_arrow_diagram_func B C (@fapp0 (Functor_cat B (Product_cat C C)) (Functor_cat B C)
  (@comp_cat_cov_func B (Product_cat C C) C Prod) (@Struct_sigma (Functor B C) (λ _ : τ (Functor B C), Functor B
  C) X Y)) Z (@one_cat_difference_cospan_transf B C C1 Prod t A T0 X Y Z f g)))))
  (@one_cat_kernel_family_annihilation_path B C (@additive_preadditive C Prod t A) C1 t (@additive_terminal_object
  C Prod t A) T0 P (@transf_arrow_diagram_func B C (@fapp0 (Functor_cat B (Product_cat C C)) (Functor_cat B C)
  (@comp_cat_cov_func B (Product_cat C C) C Prod) (@Struct_sigma (Functor B C) (λ _ : τ (Functor B C), Functor B
  C) X Y)) Z (@one_cat_difference_cospan_transf B C C1 Prod t A T0 X Y Z f g))))) (@eq_sym _ _ _ (@comp_assoc
  (Functor_cat B C) (@kernel_adjunction_family_func B C (@additive_preadditive C Prod t A) t
  (@additive_terminal_object C Prod t A) P (@transf_arrow_diagram_func B C (@fapp0 (Functor_cat B (Product_cat C
  C)) (Functor_cat B C) (@comp_cat_cov_func B (Product_cat C C) C Prod) (@Struct_sigma (Functor B C) (λ _ : τ
  (Functor B C), Functor B C) X Y)) Z (@one_cat_difference_cospan_transf B C C1 Prod t A T0 X Y Z f g))) (@fapp0
  (Functor_cat B (Product_cat C C)) (Functor_cat B C) (@comp_cat_cov_func B (Product_cat C C) C Prod)
  (@Struct_sigma (Functor B C) (λ _ : τ (Functor B C), Functor B C) X Y)) Y Z g (@one_cat_product_family_proj2 B C
  C1 Prod (@additive_binary_products C Prod t A) X Y) (@kernel_adjunction_family_inclusion_transf B C
  (@additive_preadditive C Prod t A) t (@additive_terminal_object C Prod t A) P (@transf_arrow_diagram_func B C
  (@fapp0 (Functor_cat B (Product_cat C C)) (Functor_cat B C) (@comp_cat_cov_func B (Product_cat C C) C Prod)
  (@Struct_sigma (Functor B C) (λ _ : τ (Functor B C), Functor B C) X Y)) Z (@one_cat_difference_cospan_transf B C
  C1 Prod t A T0 X Y Z f g)))))));

// The actual cokernel of the first projection annihilates the original difference kernel.
symbol one_cat_cospan_first_cokernel_input_zero [B C : Cat] (C1 : τ (IsNCat (cat_succ cat_zero) C)) [Prod :
  τ (Functor (Product_cat C C) C)] [t : τ (Obj C)] (A : τ (@AdditiveCategory C Prod t)) (T0 : τ (@TerminalObject
  (Op_cat C) t)) (P : τ (@KernelAdjunctionStructure C (@additive_preadditive C Prod t A) t
  (@additive_terminal_object C Prod t A))) (Q : τ (@CokernelAdjunctionStructure C (@additive_preadditive C Prod t
  A) t T0)) (X Y Z : τ (Functor B C)) (f : τ (@Transf B C X Z)) (g : τ (@Transf B C Y Z))
 : τ (@= (@Transf B C (@kernel_adjunction_family_func B C (@additive_preadditive C Prod t A) t
  (@additive_terminal_object C Prod t A) P (@transf_arrow_diagram_func B C (@fapp0 (Functor_cat B (Product_cat C
  C)) (Functor_cat B C) (@comp_cat_cov_func B (Product_cat C C) C Prod) (@Struct_sigma (Functor B C) (λ _ : τ
  (Functor B C), Functor B C) X Y)) Z (@one_cat_difference_cospan_transf B C C1 Prod t A T0 X Y Z f g)))
  (@cokernel_adjunction_family_func B C (@additive_preadditive C Prod t A) t T0 Q (@transf_arrow_diagram_func B C
  (@kernel_adjunction_family_func B C (@additive_preadditive C Prod t A) t (@additive_terminal_object C Prod t A)
  P (@transf_arrow_diagram_func B C (@fapp0 (Functor_cat B (Product_cat C C)) (Functor_cat B C)
  (@comp_cat_cov_func B (Product_cat C C) C Prod) (@Struct_sigma (Functor B C) (λ _ : τ (Functor B C), Functor B
  C) X Y)) Z (@one_cat_difference_cospan_transf B C C1 Prod t A T0 X Y Z f g))) X
  (@one_cat_cospan_kernel_first B C C1 Prod t A T0 P Q X Y Z f g)))) (@comp_fapp0 (Functor_cat B C)
  (@kernel_adjunction_family_func B C (@additive_preadditive C Prod t A) t (@additive_terminal_object C Prod t A)
  P (@transf_arrow_diagram_func B C (@fapp0 (Functor_cat B (Product_cat C C)) (Functor_cat B C)
  (@comp_cat_cov_func B (Product_cat C C) C Prod) (@Struct_sigma (Functor B C) (λ _ : τ (Functor B C), Functor B
  C) X Y)) Z (@one_cat_difference_cospan_transf B C C1 Prod t A T0 X Y Z f g))) (@fapp0 (Functor_cat B
  (Product_cat C C)) (Functor_cat B C) (@comp_cat_cov_func B (Product_cat C C) C Prod) (@Struct_sigma (Functor B
  C) (λ _ : τ (Functor B C), Functor B C) X Y)) (@cokernel_adjunction_family_func B C (@additive_preadditive C
  Prod t A) t T0 Q (@transf_arrow_diagram_func B C (@kernel_adjunction_family_func B C (@additive_preadditive C
  Prod t A) t (@additive_terminal_object C Prod t A) P (@transf_arrow_diagram_func B C (@fapp0 (Functor_cat B
  (Product_cat C C)) (Functor_cat B C) (@comp_cat_cov_func B (Product_cat C C) C Prod) (@Struct_sigma (Functor B
  C) (λ _ : τ (Functor B C), Functor B C) X Y)) Z (@one_cat_difference_cospan_transf B C C1 Prod t A T0 X Y Z f
  g))) X (@one_cat_cospan_kernel_first B C C1 Prod t A T0 P Q X Y Z f g))) (@comp_fapp0 (Functor_cat B C)
  (@fapp0 (Functor_cat B (Product_cat C C)) (Functor_cat B C) (@comp_cat_cov_func B (Product_cat C C) C Prod)
  (@Struct_sigma (Functor B C) (λ _ : τ (Functor B C), Functor B C) X Y)) X (@cokernel_adjunction_family_func B C
  (@additive_preadditive C Prod t A) t T0 Q (@transf_arrow_diagram_func B C (@kernel_adjunction_family_func B C
  (@additive_preadditive C Prod t A) t (@additive_terminal_object C Prod t A) P (@transf_arrow_diagram_func B C
  (@fapp0 (Functor_cat B (Product_cat C C)) (Functor_cat B C) (@comp_cat_cov_func B (Product_cat C C) C Prod)
  (@Struct_sigma (Functor B C) (λ _ : τ (Functor B C), Functor B C) X Y)) Z (@one_cat_difference_cospan_transf B C
  C1 Prod t A T0 X Y Z f g))) X (@one_cat_cospan_kernel_first B C C1 Prod t A T0 P Q X Y Z f g)))
  (@cokernel_adjunction_family_projection_transf B C (@additive_preadditive C Prod t A) t T0 Q
  (@transf_arrow_diagram_func B C (@kernel_adjunction_family_func B C (@additive_preadditive C Prod t A) t
  (@additive_terminal_object C Prod t A) P (@transf_arrow_diagram_func B C (@fapp0 (Functor_cat B (Product_cat C
  C)) (Functor_cat B C) (@comp_cat_cov_func B (Product_cat C C) C Prod) (@Struct_sigma (Functor B C) (λ _ : τ
  (Functor B C), Functor B C) X Y)) Z (@one_cat_difference_cospan_transf B C C1 Prod t A T0 X Y Z f g))) X
  (@one_cat_cospan_kernel_first B C C1 Prod t A T0 P Q X Y Z f g))) (@one_cat_product_family_proj1 B C C1
  Prod (@additive_binary_products C Prod t A) X Y)) (@kernel_adjunction_family_inclusion_transf B C
  (@additive_preadditive C Prod t A) t (@additive_terminal_object C Prod t A) P (@transf_arrow_diagram_func B C
  (@fapp0 (Functor_cat B (Product_cat C C)) (Functor_cat B C) (@comp_cat_cov_func B (Product_cat C C) C Prod)
  (@Struct_sigma (Functor B C) (λ _ : τ (Functor B C), Functor B C) X Y)) Z (@one_cat_difference_cospan_transf B C
  C1 Prod t A T0 X Y Z f g)))) (@zero_arrow_family_zero_transf B C t (@additive_terminal_object C Prod t A) T0
  (@kernel_adjunction_family_func B C (@additive_preadditive C Prod t A) t (@additive_terminal_object C Prod t A)
  P (@transf_arrow_diagram_func B C (@fapp0 (Functor_cat B (Product_cat C C)) (Functor_cat B C)
  (@comp_cat_cov_func B (Product_cat C C) C Prod) (@Struct_sigma (Functor B C) (λ _ : τ (Functor B C), Functor B
  C) X Y)) Z (@one_cat_difference_cospan_transf B C C1 Prod t A T0 X Y Z f g))) (@cokernel_adjunction_family_func
  B C (@additive_preadditive C Prod t A) t T0 Q (@transf_arrow_diagram_func B C (@kernel_adjunction_family_func B
  C (@additive_preadditive C Prod t A) t (@additive_terminal_object C Prod t A) P (@transf_arrow_diagram_func B C
  (@fapp0 (Functor_cat B (Product_cat C C)) (Functor_cat B C) (@comp_cat_cov_func B (Product_cat C C) C Prod)
  (@Struct_sigma (Functor B C) (λ _ : τ (Functor B C), Functor B C) X Y)) Z (@one_cat_difference_cospan_transf B C
  C1 Prod t A T0 X Y Z f g))) X (@one_cat_cospan_kernel_first B C C1 Prod t A T0 P Q X Y Z f g)))))
≔ (@eq_trans _ _ _ _ (@eq_sym _ _ _ (@comp_assoc (Functor_cat B C) (@kernel_adjunction_family_func B C
  (@additive_preadditive C Prod t A) t (@additive_terminal_object C Prod t A) P (@transf_arrow_diagram_func B C
  (@fapp0 (Functor_cat B (Product_cat C C)) (Functor_cat B C) (@comp_cat_cov_func B (Product_cat C C) C Prod)
  (@Struct_sigma (Functor B C) (λ _ : τ (Functor B C), Functor B C) X Y)) Z (@one_cat_difference_cospan_transf B C
  C1 Prod t A T0 X Y Z f g))) (@fapp0 (Functor_cat B (Product_cat C C)) (Functor_cat B C) (@comp_cat_cov_func B
  (Product_cat C C) C Prod) (@Struct_sigma (Functor B C) (λ _ : τ (Functor B C), Functor B C) X Y)) X
  (@cokernel_adjunction_family_func B C (@additive_preadditive C Prod t A) t T0 Q (@transf_arrow_diagram_func B C
  (@kernel_adjunction_family_func B C (@additive_preadditive C Prod t A) t (@additive_terminal_object C Prod t A)
  P (@transf_arrow_diagram_func B C (@fapp0 (Functor_cat B (Product_cat C C)) (Functor_cat B C)
  (@comp_cat_cov_func B (Product_cat C C) C Prod) (@Struct_sigma (Functor B C) (λ _ : τ (Functor B C), Functor B
  C) X Y)) Z (@one_cat_difference_cospan_transf B C C1 Prod t A T0 X Y Z f g))) X
  (@one_cat_cospan_kernel_first B C C1 Prod t A T0 P Q X Y Z f g)))
  (@cokernel_adjunction_family_projection_transf B C (@additive_preadditive C Prod t A) t T0 Q
  (@transf_arrow_diagram_func B C (@kernel_adjunction_family_func B C (@additive_preadditive C Prod t A) t
  (@additive_terminal_object C Prod t A) P (@transf_arrow_diagram_func B C (@fapp0 (Functor_cat B (Product_cat C
  C)) (Functor_cat B C) (@comp_cat_cov_func B (Product_cat C C) C Prod) (@Struct_sigma (Functor B C) (λ _ : τ
  (Functor B C), Functor B C) X Y)) Z (@one_cat_difference_cospan_transf B C C1 Prod t A T0 X Y Z f g))) X
  (@one_cat_cospan_kernel_first B C C1 Prod t A T0 P Q X Y Z f g))) (@one_cat_product_family_proj1 B C C1
  Prod (@additive_binary_products C Prod t A) X Y) (@kernel_adjunction_family_inclusion_transf B C
  (@additive_preadditive C Prod t A) t (@additive_terminal_object C Prod t A) P (@transf_arrow_diagram_func B C
  (@fapp0 (Functor_cat B (Product_cat C C)) (Functor_cat B C) (@comp_cat_cov_func B (Product_cat C C) C Prod)
  (@Struct_sigma (Functor B C) (λ _ : τ (Functor B C), Functor B C) X Y)) Z (@one_cat_difference_cospan_transf B C
  C1 Prod t A T0 X Y Z f g))))) (@one_cat_cokernel_family_annihilation_path B C (@additive_preadditive C Prod t A)
  C1 t (@additive_terminal_object C Prod t A) T0 Q (@transf_arrow_diagram_func B C (@kernel_adjunction_family_func
  B C (@additive_preadditive C Prod t A) t (@additive_terminal_object C Prod t A) P (@transf_arrow_diagram_func B
  C (@fapp0 (Functor_cat B (Product_cat C C)) (Functor_cat B C) (@comp_cat_cov_func B (Product_cat C C) C Prod)
  (@Struct_sigma (Functor B C) (λ _ : τ (Functor B C), Functor B C) X Y)) Z (@one_cat_difference_cospan_transf B C
  C1 Prod t A T0 X Y Z f g))) X (@one_cat_cospan_kernel_first B C C1 Prod t A T0 P Q X Y Z f g))));

// Descend the original cokernel input through the derived difference cover.
symbol one_cat_cospan_first_cokernel_descent [B C : Cat] (C1 : τ (IsNCat (cat_succ cat_zero) C)) [Prod : τ
  (Functor (Product_cat C C) C)] [t : τ (Obj C)] (A : τ (@AdditiveCategory C Prod t)) (T0 : τ (@TerminalObject
  (Op_cat C) t)) (P : τ (@KernelAdjunctionStructure C (@additive_preadditive C Prod t A) t
  (@additive_terminal_object C Prod t A))) (Q : τ (@CokernelAdjunctionStructure C (@additive_preadditive C Prod t
  A) t T0)) (N : τ (@OneCatAdjunctionNormality C (@additive_preadditive C Prod t A) C1 t
  (@additive_terminal_object C Prod t A) T0 P Q)) (X Y Z : τ (Functor B C)) (f : τ (@Transf B C X Z)) (g : τ
  (@Transf B C Y Z)) (zg : τ (@= (@Transf B C Z (@cokernel_adjunction_family_func B C (@additive_preadditive C
  Prod t A) t T0 Q (@transf_arrow_diagram_func B C Y Z g))) (@cokernel_adjunction_family_projection_transf B C
  (@additive_preadditive C Prod t A) t T0 Q (@transf_arrow_diagram_func B C Y Z g))
  (@zero_arrow_family_zero_transf B C t (@additive_terminal_object C Prod t A) T0 Z
  (@cokernel_adjunction_family_func B C (@additive_preadditive C Prod t A) t T0 Q (@transf_arrow_diagram_func B C
  Y Z g)))))
 : τ (@Transf B C Z (@cokernel_adjunction_family_func B C (@additive_preadditive C Prod t A) t T0 Q
  (@transf_arrow_diagram_func B C (@kernel_adjunction_family_func B C (@additive_preadditive C Prod t A) t
  (@additive_terminal_object C Prod t A) P (@transf_arrow_diagram_func B C (@fapp0 (Functor_cat B (Product_cat C
  C)) (Functor_cat B C) (@comp_cat_cov_func B (Product_cat C C) C Prod) (@Struct_sigma (Functor B C) (λ _ : τ
  (Functor B C), Functor B C) X Y)) Z (@one_cat_difference_cospan_transf B C C1 Prod t A T0 X Y Z f g))) X
  (@one_cat_cospan_kernel_first B C C1 Prod t A T0 P Q X Y Z f g))))
≔ @one_cat_coimage_cover_descent B C (@additive_preadditive C Prod t A) C1 t (@additive_terminal_object C Prod t
  A) T0 P Q (@transf_arrow_diagram_func B C (@fapp0 (Functor_cat B (Product_cat C C)) (Functor_cat B C)
  (@comp_cat_cov_func B (Product_cat C C) C Prod) (@Struct_sigma (Functor B C) (λ _ : τ (Functor B C), Functor B
  C) X Y)) Z (@one_cat_difference_cospan_transf B C C1 Prod t A T0 X Y Z f g))
  (@one_cat_difference_cospan_zero_cokernel_cover B C C1 Prod t A T0 P Q N X Y Z f g zg)
  (@cokernel_adjunction_family_func B C (@additive_preadditive C Prod t A) t T0 Q (@transf_arrow_diagram_func B C
  (@kernel_adjunction_family_func B C (@additive_preadditive C Prod t A) t (@additive_terminal_object C Prod t A)
  P (@transf_arrow_diagram_func B C (@fapp0 (Functor_cat B (Product_cat C C)) (Functor_cat B C)
  (@comp_cat_cov_func B (Product_cat C C) C Prod) (@Struct_sigma (Functor B C) (λ _ : τ (Functor B C), Functor B
  C) X Y)) Z (@one_cat_difference_cospan_transf B C C1 Prod t A T0 X Y Z f g))) X
  (@one_cat_cospan_kernel_first B C C1 Prod t A T0 P Q X Y Z f g))) (@comp_fapp0 (Functor_cat B C) (@fapp0
  (Functor_cat B (Product_cat C C)) (Functor_cat B C) (@comp_cat_cov_func B (Product_cat C C) C Prod)
  (@Struct_sigma (Functor B C) (λ _ : τ (Functor B C), Functor B C) X Y)) X (@cokernel_adjunction_family_func B C
  (@additive_preadditive C Prod t A) t T0 Q (@transf_arrow_diagram_func B C (@kernel_adjunction_family_func B C
  (@additive_preadditive C Prod t A) t (@additive_terminal_object C Prod t A) P (@transf_arrow_diagram_func B C
  (@fapp0 (Functor_cat B (Product_cat C C)) (Functor_cat B C) (@comp_cat_cov_func B (Product_cat C C) C Prod)
  (@Struct_sigma (Functor B C) (λ _ : τ (Functor B C), Functor B C) X Y)) Z (@one_cat_difference_cospan_transf B C
  C1 Prod t A T0 X Y Z f g))) X (@one_cat_cospan_kernel_first B C C1 Prod t A T0 P Q X Y Z f g)))
  (@cokernel_adjunction_family_projection_transf B C (@additive_preadditive C Prod t A) t T0 Q
  (@transf_arrow_diagram_func B C (@kernel_adjunction_family_func B C (@additive_preadditive C Prod t A) t
  (@additive_terminal_object C Prod t A) P (@transf_arrow_diagram_func B C (@fapp0 (Functor_cat B (Product_cat C
  C)) (Functor_cat B C) (@comp_cat_cov_func B (Product_cat C C) C Prod) (@Struct_sigma (Functor B C) (λ _ : τ
  (Functor B C), Functor B C) X Y)) Z (@one_cat_difference_cospan_transf B C C1 Prod t A T0 X Y Z f g))) X
  (@one_cat_cospan_kernel_first B C C1 Prod t A T0 P Q X Y Z f g))) (@one_cat_product_family_proj1 B C C1
  Prod (@additive_binary_products C Prod t A) X Y)) (@one_cat_cospan_first_cokernel_input_zero B C C1 Prod t
  A T0 P Q X Y Z f g);

// The original auxiliary cover reconstructs that same whole input.
symbol one_cat_cospan_first_cokernel_descent_path [B C : Cat] (C1 : τ (IsNCat (cat_succ cat_zero) C)) [Prod
  : τ (Functor (Product_cat C C) C)] [t : τ (Obj C)] (A : τ (@AdditiveCategory C Prod t)) (T0 : τ (@TerminalObject
  (Op_cat C) t)) (P : τ (@KernelAdjunctionStructure C (@additive_preadditive C Prod t A) t
  (@additive_terminal_object C Prod t A))) (Q : τ (@CokernelAdjunctionStructure C (@additive_preadditive C Prod t
  A) t T0)) (N : τ (@OneCatAdjunctionNormality C (@additive_preadditive C Prod t A) C1 t
  (@additive_terminal_object C Prod t A) T0 P Q)) (X Y Z : τ (Functor B C)) (f : τ (@Transf B C X Z)) (g : τ
  (@Transf B C Y Z)) (zg : τ (@= (@Transf B C Z (@cokernel_adjunction_family_func B C (@additive_preadditive C
  Prod t A) t T0 Q (@transf_arrow_diagram_func B C Y Z g))) (@cokernel_adjunction_family_projection_transf B C
  (@additive_preadditive C Prod t A) t T0 Q (@transf_arrow_diagram_func B C Y Z g))
  (@zero_arrow_family_zero_transf B C t (@additive_terminal_object C Prod t A) T0 Z
  (@cokernel_adjunction_family_func B C (@additive_preadditive C Prod t A) t T0 Q (@transf_arrow_diagram_func B C
  Y Z g)))))
 : τ (@= (@Transf B C (@fapp0 (Functor_cat B (Product_cat C C)) (Functor_cat B C) (@comp_cat_cov_func B
  (Product_cat C C) C Prod) (@Struct_sigma (Functor B C) (λ _ : τ (Functor B C), Functor B C) X Y))
  (@cokernel_adjunction_family_func B C (@additive_preadditive C Prod t A) t T0 Q (@transf_arrow_diagram_func B C
  (@kernel_adjunction_family_func B C (@additive_preadditive C Prod t A) t (@additive_terminal_object C Prod t A)
  P (@transf_arrow_diagram_func B C (@fapp0 (Functor_cat B (Product_cat C C)) (Functor_cat B C)
  (@comp_cat_cov_func B (Product_cat C C) C Prod) (@Struct_sigma (Functor B C) (λ _ : τ (Functor B C), Functor B
  C) X Y)) Z (@one_cat_difference_cospan_transf B C C1 Prod t A T0 X Y Z f g))) X
  (@one_cat_cospan_kernel_first B C C1 Prod t A T0 P Q X Y Z f g)))) (@comp_fapp0 (Functor_cat B C) (@fapp0
  (Functor_cat B (Product_cat C C)) (Functor_cat B C) (@comp_cat_cov_func B (Product_cat C C) C Prod)
  (@Struct_sigma (Functor B C) (λ _ : τ (Functor B C), Functor B C) X Y)) Z (@cokernel_adjunction_family_func B C
  (@additive_preadditive C Prod t A) t T0 Q (@transf_arrow_diagram_func B C (@kernel_adjunction_family_func B C
  (@additive_preadditive C Prod t A) t (@additive_terminal_object C Prod t A) P (@transf_arrow_diagram_func B C
  (@fapp0 (Functor_cat B (Product_cat C C)) (Functor_cat B C) (@comp_cat_cov_func B (Product_cat C C) C Prod)
  (@Struct_sigma (Functor B C) (λ _ : τ (Functor B C), Functor B C) X Y)) Z (@one_cat_difference_cospan_transf B C
  C1 Prod t A T0 X Y Z f g))) X (@one_cat_cospan_kernel_first B C C1 Prod t A T0 P Q X Y Z f g)))
  (@one_cat_cospan_first_cokernel_descent B C C1 Prod t A T0 P Q N X Y Z f g zg)
  (@one_cat_difference_cospan_transf B C C1 Prod t A T0 X Y Z f g)) (@comp_fapp0 (Functor_cat B C) (@fapp0
  (Functor_cat B (Product_cat C C)) (Functor_cat B C) (@comp_cat_cov_func B (Product_cat C C) C Prod)
  (@Struct_sigma (Functor B C) (λ _ : τ (Functor B C), Functor B C) X Y)) X (@cokernel_adjunction_family_func B C
  (@additive_preadditive C Prod t A) t T0 Q (@transf_arrow_diagram_func B C (@kernel_adjunction_family_func B C
  (@additive_preadditive C Prod t A) t (@additive_terminal_object C Prod t A) P (@transf_arrow_diagram_func B C
  (@fapp0 (Functor_cat B (Product_cat C C)) (Functor_cat B C) (@comp_cat_cov_func B (Product_cat C C) C Prod)
  (@Struct_sigma (Functor B C) (λ _ : τ (Functor B C), Functor B C) X Y)) Z (@one_cat_difference_cospan_transf B C
  C1 Prod t A T0 X Y Z f g))) X (@one_cat_cospan_kernel_first B C C1 Prod t A T0 P Q X Y Z f g)))
  (@cokernel_adjunction_family_projection_transf B C (@additive_preadditive C Prod t A) t T0 Q
  (@transf_arrow_diagram_func B C (@kernel_adjunction_family_func B C (@additive_preadditive C Prod t A) t
  (@additive_terminal_object C Prod t A) P (@transf_arrow_diagram_func B C (@fapp0 (Functor_cat B (Product_cat C
  C)) (Functor_cat B C) (@comp_cat_cov_func B (Product_cat C C) C Prod) (@Struct_sigma (Functor B C) (λ _ : τ
  (Functor B C), Functor B C) X Y)) Z (@one_cat_difference_cospan_transf B C C1 Prod t A T0 X Y Z f g))) X
  (@one_cat_cospan_kernel_first B C C1 Prod t A T0 P Q X Y Z f g))) (@one_cat_product_family_proj1 B C C1
  Prod (@additive_binary_products C Prod t A) X Y)))
≔ @one_cat_coimage_cover_descent_reconstruction B C (@additive_preadditive C Prod t A) C1 t
  (@additive_terminal_object C Prod t A) T0 P Q (@transf_arrow_diagram_func B C (@fapp0 (Functor_cat B
  (Product_cat C C)) (Functor_cat B C) (@comp_cat_cov_func B (Product_cat C C) C Prod) (@Struct_sigma (Functor B
  C) (λ _ : τ (Functor B C), Functor B C) X Y)) Z (@one_cat_difference_cospan_transf B C C1 Prod t A T0 X Y Z f
  g)) (@one_cat_difference_cospan_zero_cokernel_cover B C C1 Prod t A T0 P Q N X Y Z f g zg)
  (@cokernel_adjunction_family_func B C (@additive_preadditive C Prod t A) t T0 Q (@transf_arrow_diagram_func B C
  (@kernel_adjunction_family_func B C (@additive_preadditive C Prod t A) t (@additive_terminal_object C Prod t A)
  P (@transf_arrow_diagram_func B C (@fapp0 (Functor_cat B (Product_cat C C)) (Functor_cat B C)
  (@comp_cat_cov_func B (Product_cat C C) C Prod) (@Struct_sigma (Functor B C) (λ _ : τ (Functor B C), Functor B
  C) X Y)) Z (@one_cat_difference_cospan_transf B C C1 Prod t A T0 X Y Z f g))) X
  (@one_cat_cospan_kernel_first B C C1 Prod t A T0 P Q X Y Z f g))) (@comp_fapp0 (Functor_cat B C) (@fapp0
  (Functor_cat B (Product_cat C C)) (Functor_cat B C) (@comp_cat_cov_func B (Product_cat C C) C Prod)
  (@Struct_sigma (Functor B C) (λ _ : τ (Functor B C), Functor B C) X Y)) X (@cokernel_adjunction_family_func B C
  (@additive_preadditive C Prod t A) t T0 Q (@transf_arrow_diagram_func B C (@kernel_adjunction_family_func B C
  (@additive_preadditive C Prod t A) t (@additive_terminal_object C Prod t A) P (@transf_arrow_diagram_func B C
  (@fapp0 (Functor_cat B (Product_cat C C)) (Functor_cat B C) (@comp_cat_cov_func B (Product_cat C C) C Prod)
  (@Struct_sigma (Functor B C) (λ _ : τ (Functor B C), Functor B C) X Y)) Z (@one_cat_difference_cospan_transf B C
  C1 Prod t A T0 X Y Z f g))) X (@one_cat_cospan_kernel_first B C C1 Prod t A T0 P Q X Y Z f g)))
  (@cokernel_adjunction_family_projection_transf B C (@additive_preadditive C Prod t A) t T0 Q
  (@transf_arrow_diagram_func B C (@kernel_adjunction_family_func B C (@additive_preadditive C Prod t A) t
  (@additive_terminal_object C Prod t A) P (@transf_arrow_diagram_func B C (@fapp0 (Functor_cat B (Product_cat C
  C)) (Functor_cat B C) (@comp_cat_cov_func B (Product_cat C C) C Prod) (@Struct_sigma (Functor B C) (λ _ : τ
  (Functor B C), Functor B C) X Y)) Z (@one_cat_difference_cospan_transf B C C1 Prod t A T0 X Y Z f g))) X
  (@one_cat_cospan_kernel_first B C C1 Prod t A T0 P Q X Y Z f g))) (@one_cat_product_family_proj1 B C C1
  Prod (@additive_binary_products C Prod t A) X Y)) (@one_cat_cospan_first_cokernel_input_zero B C C1 Prod t
  A T0 P Q X Y Z f g);

// The original second injection makes the descended map annihilate g.
symbol one_cat_cospan_first_cokernel_descent_second_zero [B C : Cat] (C1 : τ (IsNCat (cat_succ cat_zero) C))
  [Prod : τ (Functor (Product_cat C C) C)] [t : τ (Obj C)] (A : τ (@AdditiveCategory C Prod t)) (T0 : τ
  (@TerminalObject (Op_cat C) t)) (P : τ (@KernelAdjunctionStructure C (@additive_preadditive C Prod t A) t
  (@additive_terminal_object C Prod t A))) (Q : τ (@CokernelAdjunctionStructure C (@additive_preadditive C Prod t
  A) t T0)) (N : τ (@OneCatAdjunctionNormality C (@additive_preadditive C Prod t A) C1 t
  (@additive_terminal_object C Prod t A) T0 P Q)) (X Y Z : τ (Functor B C)) (f : τ (@Transf B C X Z)) (g : τ
  (@Transf B C Y Z)) (zg : τ (@= (@Transf B C Z (@cokernel_adjunction_family_func B C (@additive_preadditive C
  Prod t A) t T0 Q (@transf_arrow_diagram_func B C Y Z g))) (@cokernel_adjunction_family_projection_transf B C
  (@additive_preadditive C Prod t A) t T0 Q (@transf_arrow_diagram_func B C Y Z g))
  (@zero_arrow_family_zero_transf B C t (@additive_terminal_object C Prod t A) T0 Z
  (@cokernel_adjunction_family_func B C (@additive_preadditive C Prod t A) t T0 Q (@transf_arrow_diagram_func B C
  Y Z g)))))
 : τ (@= (@Transf B C Y (@cokernel_adjunction_family_func B C (@additive_preadditive C Prod t A) t T0 Q
  (@transf_arrow_diagram_func B C (@kernel_adjunction_family_func B C (@additive_preadditive C Prod t A) t
  (@additive_terminal_object C Prod t A) P (@transf_arrow_diagram_func B C (@fapp0 (Functor_cat B (Product_cat C
  C)) (Functor_cat B C) (@comp_cat_cov_func B (Product_cat C C) C Prod) (@Struct_sigma (Functor B C) (λ _ : τ
  (Functor B C), Functor B C) X Y)) Z (@one_cat_difference_cospan_transf B C C1 Prod t A T0 X Y Z f g))) X
  (@one_cat_cospan_kernel_first B C C1 Prod t A T0 P Q X Y Z f g)))) (@comp_fapp0 (Functor_cat B C) Y Z
  (@cokernel_adjunction_family_func B C (@additive_preadditive C Prod t A) t T0 Q (@transf_arrow_diagram_func B C
  (@kernel_adjunction_family_func B C (@additive_preadditive C Prod t A) t (@additive_terminal_object C Prod t A)
  P (@transf_arrow_diagram_func B C (@fapp0 (Functor_cat B (Product_cat C C)) (Functor_cat B C)
  (@comp_cat_cov_func B (Product_cat C C) C Prod) (@Struct_sigma (Functor B C) (λ _ : τ (Functor B C), Functor B
  C) X Y)) Z (@one_cat_difference_cospan_transf B C C1 Prod t A T0 X Y Z f g))) X
  (@one_cat_cospan_kernel_first B C C1 Prod t A T0 P Q X Y Z f g)))
  (@one_cat_cospan_first_cokernel_descent B C C1 Prod t A T0 P Q N X Y Z f g zg) g)
  (@zero_arrow_family_zero_transf B C t (@additive_terminal_object C Prod t A) T0 Y
  (@cokernel_adjunction_family_func B C (@additive_preadditive C Prod t A) t T0 Q (@transf_arrow_diagram_func B C
  (@kernel_adjunction_family_func B C (@additive_preadditive C Prod t A) t (@additive_terminal_object C Prod t A)
  P (@transf_arrow_diagram_func B C (@fapp0 (Functor_cat B (Product_cat C C)) (Functor_cat B C)
  (@comp_cat_cov_func B (Product_cat C C) C Prod) (@Struct_sigma (Functor B C) (λ _ : τ (Functor B C), Functor B
  C) X Y)) Z (@one_cat_difference_cospan_transf B C C1 Prod t A T0 X Y Z f g))) X
  (@one_cat_cospan_kernel_first B C C1 Prod t A T0 P Q X Y Z f g)))))
≔ @one_cat_difference_cospan_second_from_factor_path B C C1 Prod t A T0 X Y Z (@cokernel_adjunction_family_func B
  C (@additive_preadditive C Prod t A) t T0 Q (@transf_arrow_diagram_func B C (@kernel_adjunction_family_func B C
  (@additive_preadditive C Prod t A) t (@additive_terminal_object C Prod t A) P (@transf_arrow_diagram_func B C
  (@fapp0 (Functor_cat B (Product_cat C C)) (Functor_cat B C) (@comp_cat_cov_func B (Product_cat C C) C Prod)
  (@Struct_sigma (Functor B C) (λ _ : τ (Functor B C), Functor B C) X Y)) Z (@one_cat_difference_cospan_transf B C
  C1 Prod t A T0 X Y Z f g))) X (@one_cat_cospan_kernel_first B C C1 Prod t A T0 P Q X Y Z f g))) f g
  (@one_cat_cospan_first_cokernel_descent B C C1 Prod t A T0 P Q N X Y Z f g zg)
  (@cokernel_adjunction_family_projection_transf B C (@additive_preadditive C Prod t A) t T0 Q
  (@transf_arrow_diagram_func B C (@kernel_adjunction_family_func B C (@additive_preadditive C Prod t A) t
  (@additive_terminal_object C Prod t A) P (@transf_arrow_diagram_func B C (@fapp0 (Functor_cat B (Product_cat C
  C)) (Functor_cat B C) (@comp_cat_cov_func B (Product_cat C C) C Prod) (@Struct_sigma (Functor B C) (λ _ : τ
  (Functor B C), Functor B C) X Y)) Z (@one_cat_difference_cospan_transf B C C1 Prod t A T0 X Y Z f g))) X
  (@one_cat_cospan_kernel_first B C C1 Prod t A T0 P Q X Y Z f g)))
  (@one_cat_cospan_first_cokernel_descent_path B C C1 Prod t A T0 P Q N X Y Z f g zg);

// The derived original g cancellation forces the descended map to zero.
symbol one_cat_cospan_first_cokernel_descent_zero [B C : Cat] (C1 : τ (IsNCat (cat_succ cat_zero) C)) [Prod
  : τ (Functor (Product_cat C C) C)] [t : τ (Obj C)] (A : τ (@AdditiveCategory C Prod t)) (T0 : τ (@TerminalObject
  (Op_cat C) t)) (P : τ (@KernelAdjunctionStructure C (@additive_preadditive C Prod t A) t
  (@additive_terminal_object C Prod t A))) (Q : τ (@CokernelAdjunctionStructure C (@additive_preadditive C Prod t
  A) t T0)) (N : τ (@OneCatAdjunctionNormality C (@additive_preadditive C Prod t A) C1 t
  (@additive_terminal_object C Prod t A) T0 P Q)) (X Y Z : τ (Functor B C)) (f : τ (@Transf B C X Z)) (g : τ
  (@Transf B C Y Z)) (zg : τ (@= (@Transf B C Z (@cokernel_adjunction_family_func B C (@additive_preadditive C
  Prod t A) t T0 Q (@transf_arrow_diagram_func B C Y Z g))) (@cokernel_adjunction_family_projection_transf B C
  (@additive_preadditive C Prod t A) t T0 Q (@transf_arrow_diagram_func B C Y Z g))
  (@zero_arrow_family_zero_transf B C t (@additive_terminal_object C Prod t A) T0 Z
  (@cokernel_adjunction_family_func B C (@additive_preadditive C Prod t A) t T0 Q (@transf_arrow_diagram_func B C
  Y Z g)))))
 : τ (@= (@Transf B C Z (@cokernel_adjunction_family_func B C (@additive_preadditive C Prod t A) t T0 Q
  (@transf_arrow_diagram_func B C (@kernel_adjunction_family_func B C (@additive_preadditive C Prod t A) t
  (@additive_terminal_object C Prod t A) P (@transf_arrow_diagram_func B C (@fapp0 (Functor_cat B (Product_cat C
  C)) (Functor_cat B C) (@comp_cat_cov_func B (Product_cat C C) C Prod) (@Struct_sigma (Functor B C) (λ _ : τ
  (Functor B C), Functor B C) X Y)) Z (@one_cat_difference_cospan_transf B C C1 Prod t A T0 X Y Z f g))) X
  (@one_cat_cospan_kernel_first B C C1 Prod t A T0 P Q X Y Z f g))))
  (@one_cat_cospan_first_cokernel_descent B C C1 Prod t A T0 P Q N X Y Z f g zg)
  (@zero_arrow_family_zero_transf B C t (@additive_terminal_object C Prod t A) T0 Z
  (@cokernel_adjunction_family_func B C (@additive_preadditive C Prod t A) t T0 Q (@transf_arrow_diagram_func B C
  (@kernel_adjunction_family_func B C (@additive_preadditive C Prod t A) t (@additive_terminal_object C Prod t A)
  P (@transf_arrow_diagram_func B C (@fapp0 (Functor_cat B (Product_cat C C)) (Functor_cat B C)
  (@comp_cat_cov_func B (Product_cat C C) C Prod) (@Struct_sigma (Functor B C) (λ _ : τ (Functor B C), Functor B
  C) X Y)) Z (@one_cat_difference_cospan_transf B C C1 Prod t A T0 X Y Z f g))) X
  (@one_cat_cospan_kernel_first B C C1 Prod t A T0 P Q X Y Z f g)))))
≔ @one_cat_coimage_cover_reflect_path B C (@additive_preadditive C Prod t A) C1 t (@additive_terminal_object C
  Prod t A) T0 P Q (@transf_arrow_diagram_func B C Y Z g) (@one_cat_zero_cokernel_cover_omega B C
  (@additive_preadditive C Prod t A) C1 t (@additive_terminal_object C Prod t A) T0 P Q N
  (@transf_arrow_diagram_func B C Y Z g) zg) (@cokernel_adjunction_family_func B C (@additive_preadditive C Prod t
  A) t T0 Q (@transf_arrow_diagram_func B C (@kernel_adjunction_family_func B C (@additive_preadditive C Prod t A)
  t (@additive_terminal_object C Prod t A) P (@transf_arrow_diagram_func B C (@fapp0 (Functor_cat B (Product_cat C
  C)) (Functor_cat B C) (@comp_cat_cov_func B (Product_cat C C) C Prod) (@Struct_sigma (Functor B C) (λ _ : τ
  (Functor B C), Functor B C) X Y)) Z (@one_cat_difference_cospan_transf B C C1 Prod t A T0 X Y Z f g))) X
  (@one_cat_cospan_kernel_first B C C1 Prod t A T0 P Q X Y Z f g)))
  (@one_cat_cospan_first_cokernel_descent B C C1 Prod t A T0 P Q N X Y Z f g zg)
  (@zero_arrow_family_zero_transf B C t (@additive_terminal_object C Prod t A) T0 Z
  (@cokernel_adjunction_family_func B C (@additive_preadditive C Prod t A) t T0 Q (@transf_arrow_diagram_func B C
  (@kernel_adjunction_family_func B C (@additive_preadditive C Prod t A) t (@additive_terminal_object C Prod t A)
  P (@transf_arrow_diagram_func B C (@fapp0 (Functor_cat B (Product_cat C C)) (Functor_cat B C)
  (@comp_cat_cov_func B (Product_cat C C) C Prod) (@Struct_sigma (Functor B C) (λ _ : τ (Functor B C), Functor B
  C) X Y)) Z (@one_cat_difference_cospan_transf B C C1 Prod t A T0 X Y Z f g))) X
  (@one_cat_cospan_kernel_first B C C1 Prod t A T0 P Q X Y Z f g)))) (@eq_trans _ _ _ _
  (@one_cat_cospan_first_cokernel_descent_second_zero B C C1 Prod t A T0 P Q N X Y Z f g zg) (@eq_sym _ _ _
  (@one_cat_zero_family_precompose_path B C C1 t (@additive_terminal_object C Prod t A) T0 Y Z
  (@cokernel_adjunction_family_func B C (@additive_preadditive C Prod t A) t T0 Q (@transf_arrow_diagram_func B C
  (@kernel_adjunction_family_func B C (@additive_preadditive C Prod t A) t (@additive_terminal_object C Prod t A)
  P (@transf_arrow_diagram_func B C (@fapp0 (Functor_cat B (Product_cat C C)) (Functor_cat B C)
  (@comp_cat_cov_func B (Product_cat C C) C Prod) (@Struct_sigma (Functor B C) (λ _ : τ (Functor B C), Functor B
  C) X Y)) Z (@one_cat_difference_cospan_transf B C C1 Prod t A T0 X Y Z f g))) X
  (@one_cat_cospan_kernel_first B C C1 Prod t A T0 P Q X Y Z f g))) g)));

// The original first injection makes the actual first-projection cokernel zero.
symbol one_cat_cospan_kernel_first_cokernel_zero [B C : Cat] (C1 : τ (IsNCat (cat_succ cat_zero) C)) [Prod :
  τ (Functor (Product_cat C C) C)] [t : τ (Obj C)] (A : τ (@AdditiveCategory C Prod t)) (T0 : τ (@TerminalObject
  (Op_cat C) t)) (P : τ (@KernelAdjunctionStructure C (@additive_preadditive C Prod t A) t
  (@additive_terminal_object C Prod t A))) (Q : τ (@CokernelAdjunctionStructure C (@additive_preadditive C Prod t
  A) t T0)) (N : τ (@OneCatAdjunctionNormality C (@additive_preadditive C Prod t A) C1 t
  (@additive_terminal_object C Prod t A) T0 P Q)) (X Y Z : τ (Functor B C)) (f : τ (@Transf B C X Z)) (g : τ
  (@Transf B C Y Z)) (zg : τ (@= (@Transf B C Z (@cokernel_adjunction_family_func B C (@additive_preadditive C
  Prod t A) t T0 Q (@transf_arrow_diagram_func B C Y Z g))) (@cokernel_adjunction_family_projection_transf B C
  (@additive_preadditive C Prod t A) t T0 Q (@transf_arrow_diagram_func B C Y Z g))
  (@zero_arrow_family_zero_transf B C t (@additive_terminal_object C Prod t A) T0 Z
  (@cokernel_adjunction_family_func B C (@additive_preadditive C Prod t A) t T0 Q (@transf_arrow_diagram_func B C
  Y Z g)))))
 : τ (@= (@Transf B C X (@cokernel_adjunction_family_func B C (@additive_preadditive C Prod t A) t T0 Q
  (@transf_arrow_diagram_func B C (@kernel_adjunction_family_func B C (@additive_preadditive C Prod t A) t
  (@additive_terminal_object C Prod t A) P (@transf_arrow_diagram_func B C (@fapp0 (Functor_cat B (Product_cat C
  C)) (Functor_cat B C) (@comp_cat_cov_func B (Product_cat C C) C Prod) (@Struct_sigma (Functor B C) (λ _ : τ
  (Functor B C), Functor B C) X Y)) Z (@one_cat_difference_cospan_transf B C C1 Prod t A T0 X Y Z f g))) X
  (@one_cat_cospan_kernel_first B C C1 Prod t A T0 P Q X Y Z f g))))
  (@cokernel_adjunction_family_projection_transf B C (@additive_preadditive C Prod t A) t T0 Q
  (@transf_arrow_diagram_func B C (@kernel_adjunction_family_func B C (@additive_preadditive C Prod t A) t
  (@additive_terminal_object C Prod t A) P (@transf_arrow_diagram_func B C (@fapp0 (Functor_cat B (Product_cat C
  C)) (Functor_cat B C) (@comp_cat_cov_func B (Product_cat C C) C Prod) (@Struct_sigma (Functor B C) (λ _ : τ
  (Functor B C), Functor B C) X Y)) Z (@one_cat_difference_cospan_transf B C C1 Prod t A T0 X Y Z f g))) X
  (@one_cat_cospan_kernel_first B C C1 Prod t A T0 P Q X Y Z f g))) (@zero_arrow_family_zero_transf B C t
  (@additive_terminal_object C Prod t A) T0 X (@cokernel_adjunction_family_func B C (@additive_preadditive C Prod
  t A) t T0 Q (@transf_arrow_diagram_func B C (@kernel_adjunction_family_func B C (@additive_preadditive C Prod t
  A) t (@additive_terminal_object C Prod t A) P (@transf_arrow_diagram_func B C (@fapp0 (Functor_cat B
  (Product_cat C C)) (Functor_cat B C) (@comp_cat_cov_func B (Product_cat C C) C Prod) (@Struct_sigma (Functor B
  C) (λ _ : τ (Functor B C), Functor B C) X Y)) Z (@one_cat_difference_cospan_transf B C C1 Prod t A T0 X Y Z f
  g))) X (@one_cat_cospan_kernel_first B C C1 Prod t A T0 P Q X Y Z f g)))))
≔ @one_cat_product_first_zero_reflect_path B C C1 Prod t A T0 X Y (@cokernel_adjunction_family_func B C
  (@additive_preadditive C Prod t A) t T0 Q (@transf_arrow_diagram_func B C (@kernel_adjunction_family_func B C
  (@additive_preadditive C Prod t A) t (@additive_terminal_object C Prod t A) P (@transf_arrow_diagram_func B C
  (@fapp0 (Functor_cat B (Product_cat C C)) (Functor_cat B C) (@comp_cat_cov_func B (Product_cat C C) C Prod)
  (@Struct_sigma (Functor B C) (λ _ : τ (Functor B C), Functor B C) X Y)) Z (@one_cat_difference_cospan_transf B C
  C1 Prod t A T0 X Y Z f g))) X (@one_cat_cospan_kernel_first B C C1 Prod t A T0 P Q X Y Z f g)))
  (@cokernel_adjunction_family_projection_transf B C (@additive_preadditive C Prod t A) t T0 Q
  (@transf_arrow_diagram_func B C (@kernel_adjunction_family_func B C (@additive_preadditive C Prod t A) t
  (@additive_terminal_object C Prod t A) P (@transf_arrow_diagram_func B C (@fapp0 (Functor_cat B (Product_cat C
  C)) (Functor_cat B C) (@comp_cat_cov_func B (Product_cat C C) C Prod) (@Struct_sigma (Functor B C) (λ _ : τ
  (Functor B C), Functor B C) X Y)) Z (@one_cat_difference_cospan_transf B C C1 Prod t A T0 X Y Z f g))) X
  (@one_cat_cospan_kernel_first B C C1 Prod t A T0 P Q X Y Z f g))) (@eq_trans _ _ _ _ (@eq_sym _ _ _
  (@one_cat_cospan_first_cokernel_descent_path B C C1 Prod t A T0 P Q N X Y Z f g zg)) (@eq_trans _ _ _ _
  (@eq_ap (@Transf B C Z (@cokernel_adjunction_family_func B C (@additive_preadditive C Prod t A) t T0 Q
  (@transf_arrow_diagram_func B C (@kernel_adjunction_family_func B C (@additive_preadditive C Prod t A) t
  (@additive_terminal_object C Prod t A) P (@transf_arrow_diagram_func B C (@fapp0 (Functor_cat B (Product_cat C
  C)) (Functor_cat B C) (@comp_cat_cov_func B (Product_cat C C) C Prod) (@Struct_sigma (Functor B C) (λ _ : τ
  (Functor B C), Functor B C) X Y)) Z (@one_cat_difference_cospan_transf B C C1 Prod t A T0 X Y Z f g))) X
  (@one_cat_cospan_kernel_first B C C1 Prod t A T0 P Q X Y Z f g)))) (@Transf B C (@fapp0 (Functor_cat B
  (Product_cat C C)) (Functor_cat B C) (@comp_cat_cov_func B (Product_cat C C) C Prod) (@Struct_sigma (Functor B
  C) (λ _ : τ (Functor B C), Functor B C) X Y)) (@cokernel_adjunction_family_func B C (@additive_preadditive C
  Prod t A) t T0 Q (@transf_arrow_diagram_func B C (@kernel_adjunction_family_func B C (@additive_preadditive C
  Prod t A) t (@additive_terminal_object C Prod t A) P (@transf_arrow_diagram_func B C (@fapp0 (Functor_cat B
  (Product_cat C C)) (Functor_cat B C) (@comp_cat_cov_func B (Product_cat C C) C Prod) (@Struct_sigma (Functor B
  C) (λ _ : τ (Functor B C), Functor B C) X Y)) Z (@one_cat_difference_cospan_transf B C C1 Prod t A T0 X Y Z f
  g))) X (@one_cat_cospan_kernel_first B C C1 Prod t A T0 P Q X Y Z f g)))) (λ v : τ (@Transf B C Z
  (@cokernel_adjunction_family_func B C (@additive_preadditive C Prod t A) t T0 Q (@transf_arrow_diagram_func B C
  (@kernel_adjunction_family_func B C (@additive_preadditive C Prod t A) t (@additive_terminal_object C Prod t A)
  P (@transf_arrow_diagram_func B C (@fapp0 (Functor_cat B (Product_cat C C)) (Functor_cat B C)
  (@comp_cat_cov_func B (Product_cat C C) C Prod) (@Struct_sigma (Functor B C) (λ _ : τ (Functor B C), Functor B
  C) X Y)) Z (@one_cat_difference_cospan_transf B C C1 Prod t A T0 X Y Z f g))) X
  (@one_cat_cospan_kernel_first B C C1 Prod t A T0 P Q X Y Z f g)))), (@comp_fapp0 (Functor_cat B C) (@fapp0
  (Functor_cat B (Product_cat C C)) (Functor_cat B C) (@comp_cat_cov_func B (Product_cat C C) C Prod)
  (@Struct_sigma (Functor B C) (λ _ : τ (Functor B C), Functor B C) X Y)) Z (@cokernel_adjunction_family_func B C
  (@additive_preadditive C Prod t A) t T0 Q (@transf_arrow_diagram_func B C (@kernel_adjunction_family_func B C
  (@additive_preadditive C Prod t A) t (@additive_terminal_object C Prod t A) P (@transf_arrow_diagram_func B C
  (@fapp0 (Functor_cat B (Product_cat C C)) (Functor_cat B C) (@comp_cat_cov_func B (Product_cat C C) C Prod)
  (@Struct_sigma (Functor B C) (λ _ : τ (Functor B C), Functor B C) X Y)) Z (@one_cat_difference_cospan_transf B C
  C1 Prod t A T0 X Y Z f g))) X (@one_cat_cospan_kernel_first B C C1 Prod t A T0 P Q X Y Z f g))) v
  (@one_cat_difference_cospan_transf B C C1 Prod t A T0 X Y Z f g))) (@one_cat_cospan_first_cokernel_descent
  B C C1 Prod t A T0 P Q N X Y Z f g zg) (@zero_arrow_family_zero_transf B C t (@additive_terminal_object C Prod t
  A) T0 Z (@cokernel_adjunction_family_func B C (@additive_preadditive C Prod t A) t T0 Q
  (@transf_arrow_diagram_func B C (@kernel_adjunction_family_func B C (@additive_preadditive C Prod t A) t
  (@additive_terminal_object C Prod t A) P (@transf_arrow_diagram_func B C (@fapp0 (Functor_cat B (Product_cat C
  C)) (Functor_cat B C) (@comp_cat_cov_func B (Product_cat C C) C Prod) (@Struct_sigma (Functor B C) (λ _ : τ
  (Functor B C), Functor B C) X Y)) Z (@one_cat_difference_cospan_transf B C C1 Prod t A T0 X Y Z f g))) X
  (@one_cat_cospan_kernel_first B C C1 Prod t A T0 P Q X Y Z f g))))
  (@one_cat_cospan_first_cokernel_descent_zero B C C1 Prod t A T0 P Q N X Y Z f g zg))
  (@one_cat_zero_family_precompose_path B C C1 t (@additive_terminal_object C Prod t A) T0 (@fapp0 (Functor_cat B
  (Product_cat C C)) (Functor_cat B C) (@comp_cat_cov_func B (Product_cat C C) C Prod) (@Struct_sigma (Functor B
  C) (λ _ : τ (Functor B C), Functor B C) X Y)) Z (@cokernel_adjunction_family_func B C (@additive_preadditive C
  Prod t A) t T0 Q (@transf_arrow_diagram_func B C (@kernel_adjunction_family_func B C (@additive_preadditive C
  Prod t A) t (@additive_terminal_object C Prod t A) P (@transf_arrow_diagram_func B C (@fapp0 (Functor_cat B
  (Product_cat C C)) (Functor_cat B C) (@comp_cat_cov_func B (Product_cat C C) C Prod) (@Struct_sigma (Functor B
  C) (λ _ : τ (Functor B C), Functor B C) X Y)) Z (@one_cat_difference_cospan_transf B C C1 Prod t A T0 X Y Z f
  g))) X (@one_cat_cospan_kernel_first B C C1 Prod t A T0 P Q X Y Z f g)))
  (@one_cat_difference_cospan_transf B C C1 Prod t A T0 X Y Z f g))));

// Original normality gives a categorical cover of the first projection, without a supplied cover.
symbol one_cat_cospan_kernel_first_cover [B C : Cat] (C1 : τ (IsNCat (cat_succ cat_zero) C)) [Prod : τ
  (Functor (Product_cat C C) C)] [t : τ (Obj C)] (A : τ (@AdditiveCategory C Prod t)) (T0 : τ (@TerminalObject
  (Op_cat C) t)) (P : τ (@KernelAdjunctionStructure C (@additive_preadditive C Prod t A) t
  (@additive_terminal_object C Prod t A))) (Q : τ (@CokernelAdjunctionStructure C (@additive_preadditive C Prod t
  A) t T0)) (N : τ (@OneCatAdjunctionNormality C (@additive_preadditive C Prod t A) C1 t
  (@additive_terminal_object C Prod t A) T0 P Q)) (X Y Z : τ (Functor B C)) (f : τ (@Transf B C X Z)) (g : τ
  (@Transf B C Y Z)) (zg : τ (@= (@Transf B C Z (@cokernel_adjunction_family_func B C (@additive_preadditive C
  Prod t A) t T0 Q (@transf_arrow_diagram_func B C Y Z g))) (@cokernel_adjunction_family_projection_transf B C
  (@additive_preadditive C Prod t A) t T0 Q (@transf_arrow_diagram_func B C Y Z g))
  (@zero_arrow_family_zero_transf B C t (@additive_terminal_object C Prod t A) T0 Z
  (@cokernel_adjunction_family_func B C (@additive_preadditive C Prod t A) t T0 Q (@transf_arrow_diagram_func B C
  Y Z g)))))
 : τ (@OmegaEquivAlong (Functor_cat B C) (@comp_cat_fapp0 B (Functor_cat WalkingArrow_cat C) C
  (@adjunction_coimage_func C (@additive_preadditive C Prod t A) t (@additive_terminal_object C Prod t A) T0 P Q)
  (@transf_arrow_diagram_func B C (@kernel_adjunction_family_func B C (@additive_preadditive C Prod t A) t
  (@additive_terminal_object C Prod t A) P (@transf_arrow_diagram_func B C (@fapp0 (Functor_cat B (Product_cat C
  C)) (Functor_cat B C) (@comp_cat_cov_func B (Product_cat C C) C Prod) (@Struct_sigma (Functor B C) (λ _ : τ
  (Functor B C), Functor B C) X Y)) Z (@one_cat_difference_cospan_transf B C C1 Prod t A T0 X Y Z f g))) X
  (@one_cat_cospan_kernel_first B C C1 Prod t A T0 P Q X Y Z f g))) X (@fapp0 _ _ (@comp_cat_con_fapp1_func
  B (Functor_cat WalkingArrow_cat C) C (@transf_arrow_diagram_func B C (@kernel_adjunction_family_func B C
  (@additive_preadditive C Prod t A) t (@additive_terminal_object C Prod t A) P (@transf_arrow_diagram_func B C
  (@fapp0 (Functor_cat B (Product_cat C C)) (Functor_cat B C) (@comp_cat_cov_func B (Product_cat C C) C Prod)
  (@Struct_sigma (Functor B C) (λ _ : τ (Functor B C), Functor B C) X Y)) Z (@one_cat_difference_cospan_transf B C
  C1 Prod t A T0 X Y Z f g))) X (@one_cat_cospan_kernel_first B C C1 Prod t A T0 P Q X Y Z f g))
  (@adjunction_coimage_func C (@additive_preadditive C Prod t A) t (@additive_terminal_object C Prod t A) T0 P Q)
  (@diagram_evaluation_at_func WalkingArrow_cat C walking_arrow_tgt)) (@one_cat_adjunction_coimage_to_target C
  (@additive_preadditive C Prod t A) C1 t (@additive_terminal_object C Prod t A) T0 P Q)))
≔ @one_cat_zero_cokernel_cover_omega B C (@additive_preadditive C Prod t A) C1 t (@additive_terminal_object C Prod
  t A) T0 P Q N (@transf_arrow_diagram_func B C (@kernel_adjunction_family_func B C (@additive_preadditive C Prod
  t A) t (@additive_terminal_object C Prod t A) P (@transf_arrow_diagram_func B C (@fapp0 (Functor_cat B
  (Product_cat C C)) (Functor_cat B C) (@comp_cat_cov_func B (Product_cat C C) C Prod) (@Struct_sigma (Functor B
  C) (λ _ : τ (Functor B C), Functor B C) X Y)) Z (@one_cat_difference_cospan_transf B C C1 Prod t A T0 X Y Z f
  g))) X (@one_cat_cospan_kernel_first B C C1 Prod t A T0 P Q X Y Z f g))
  (@one_cat_cospan_kernel_first_cokernel_zero B C C1 Prod t A T0 P Q N X Y Z f g zg);

// The derived first cover cancels as a whole map, preserving its original projections.
symbol one_cat_cospan_kernel_first_reflect_path [B C : Cat] (C1 : τ (IsNCat (cat_succ cat_zero) C)) [Prod :
  τ (Functor (Product_cat C C) C)] [t : τ (Obj C)] (A : τ (@AdditiveCategory C Prod t)) (T0 : τ (@TerminalObject
  (Op_cat C) t)) (P : τ (@KernelAdjunctionStructure C (@additive_preadditive C Prod t A) t
  (@additive_terminal_object C Prod t A))) (Q : τ (@CokernelAdjunctionStructure C (@additive_preadditive C Prod t
  A) t T0)) (N : τ (@OneCatAdjunctionNormality C (@additive_preadditive C Prod t A) C1 t
  (@additive_terminal_object C Prod t A) T0 P Q)) (X Y Z : τ (Functor B C)) (f : τ (@Transf B C X Z)) (g : τ
  (@Transf B C Y Z)) (zg : τ (@= (@Transf B C Z (@cokernel_adjunction_family_func B C (@additive_preadditive C
  Prod t A) t T0 Q (@transf_arrow_diagram_func B C Y Z g))) (@cokernel_adjunction_family_projection_transf B C
  (@additive_preadditive C Prod t A) t T0 Q (@transf_arrow_diagram_func B C Y Z g))
  (@zero_arrow_family_zero_transf B C t (@additive_terminal_object C Prod t A) T0 Z
  (@cokernel_adjunction_family_func B C (@additive_preadditive C Prod t A) t T0 Q (@transf_arrow_diagram_func B C
  Y Z g))))) (V : τ (Functor B C)) (a b : τ (@Transf B C X V)) (e : τ (@= (@Transf B C
  (@kernel_adjunction_family_func B C (@additive_preadditive C Prod t A) t (@additive_terminal_object C Prod t A)
  P (@transf_arrow_diagram_func B C (@fapp0 (Functor_cat B (Product_cat C C)) (Functor_cat B C)
  (@comp_cat_cov_func B (Product_cat C C) C Prod) (@Struct_sigma (Functor B C) (λ _ : τ (Functor B C), Functor B
  C) X Y)) Z (@one_cat_difference_cospan_transf B C C1 Prod t A T0 X Y Z f g))) V) (@comp_fapp0 (Functor_cat B C)
  (@kernel_adjunction_family_func B C (@additive_preadditive C Prod t A) t (@additive_terminal_object C Prod t A)
  P (@transf_arrow_diagram_func B C (@fapp0 (Functor_cat B (Product_cat C C)) (Functor_cat B C)
  (@comp_cat_cov_func B (Product_cat C C) C Prod) (@Struct_sigma (Functor B C) (λ _ : τ (Functor B C), Functor B
  C) X Y)) Z (@one_cat_difference_cospan_transf B C C1 Prod t A T0 X Y Z f g))) X V a
  (@one_cat_cospan_kernel_first B C C1 Prod t A T0 P Q X Y Z f g)) (@comp_fapp0 (Functor_cat B C)
  (@kernel_adjunction_family_func B C (@additive_preadditive C Prod t A) t (@additive_terminal_object C Prod t A)
  P (@transf_arrow_diagram_func B C (@fapp0 (Functor_cat B (Product_cat C C)) (Functor_cat B C)
  (@comp_cat_cov_func B (Product_cat C C) C Prod) (@Struct_sigma (Functor B C) (λ _ : τ (Functor B C), Functor B
  C) X Y)) Z (@one_cat_difference_cospan_transf B C C1 Prod t A T0 X Y Z f g))) X V b
  (@one_cat_cospan_kernel_first B C C1 Prod t A T0 P Q X Y Z f g))))
 : τ (@= (@Transf B C X V) a b)
≔ @one_cat_coimage_cover_reflect_path B C (@additive_preadditive C Prod t A) C1 t (@additive_terminal_object C
  Prod t A) T0 P Q (@transf_arrow_diagram_func B C (@kernel_adjunction_family_func B C (@additive_preadditive C
  Prod t A) t (@additive_terminal_object C Prod t A) P (@transf_arrow_diagram_func B C (@fapp0 (Functor_cat B
  (Product_cat C C)) (Functor_cat B C) (@comp_cat_cov_func B (Product_cat C C) C Prod) (@Struct_sigma (Functor B
  C) (λ _ : τ (Functor B C), Functor B C) X Y)) Z (@one_cat_difference_cospan_transf B C C1 Prod t A T0 X Y Z f
  g))) X (@one_cat_cospan_kernel_first B C C1 Prod t A T0 P Q X Y Z f g))
  (@one_cat_cospan_kernel_first_cover B C C1 Prod t A T0 P Q N X Y Z f g zg) V a b e;
