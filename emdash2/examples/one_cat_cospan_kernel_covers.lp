require open emdash.emdash3_2_one_cat_cospan_kernel_covers;

// The projection is the original product projection after the original difference kernel.
assert [B C : Cat] (C1 : τ (IsNCat (cat_succ cat_zero) C)) [Prod : τ (Functor (Product_cat C C) C)] [t : τ (Obj
  C)] (A : τ (@AdditiveCategory C Prod t)) (T0 : τ (@TerminalObject (Op_cat C) t)) (P : τ
  (@KernelAdjunctionStructure C (@additive_preadditive C Prod t A) t (@additive_terminal_object C Prod t A))) (Q :
  τ (@CokernelAdjunctionStructure C (@additive_preadditive C Prod t A) t T0)) (X Y Z : τ (Functor B C)) (f : τ
  (@Transf B C X Z)) (g : τ (@Transf B C Y Z)) ⊢ (@one_cat_cospan_kernel_first B C C1 Prod t A T0 P Q X Y Z f g) ≡
  (@comp_fapp0 (Functor_cat B C) (@kernel_adjunction_family_func B C (@additive_preadditive C Prod t A) t
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

// The original whole cospan relation survives component observation.
assert [B C : Cat] (C1 : τ (IsNCat (cat_succ cat_zero) C)) [Prod : τ (Functor (Product_cat C C) C)] [t : τ (Obj
  C)] (A : τ (@AdditiveCategory C Prod t)) (T0 : τ (@TerminalObject (Op_cat C) t)) (P : τ
  (@KernelAdjunctionStructure C (@additive_preadditive C Prod t A) t (@additive_terminal_object C Prod t A))) (Q :
  τ (@CokernelAdjunctionStructure C (@additive_preadditive C Prod t A) t T0)) (X Y Z : τ (Functor B C)) (f : τ
  (@Transf B C X Z)) (g : τ (@Transf B C Y Z)) (x : τ (Obj B)) ⊢ @eq_ap (@Transf B C
  (@kernel_adjunction_family_func B C (@additive_preadditive C Prod t A) t (@additive_terminal_object C Prod t A)
  P (@transf_arrow_diagram_func B C (@fapp0 (Functor_cat B (Product_cat C C)) (Functor_cat B C)
  (@comp_cat_cov_func B (Product_cat C C) C Prod) (@Struct_sigma (Functor B C) (λ _ : τ (Functor B C), Functor B
  C) X Y)) Z (@one_cat_difference_cospan_transf B C C1 Prod t A T0 X Y Z f g))) Z) (Hom C (@fapp0 B C
  (@kernel_adjunction_family_func B C (@additive_preadditive C Prod t A) t (@additive_terminal_object C Prod t A)
  P (@transf_arrow_diagram_func B C (@fapp0 (Functor_cat B (Product_cat C C)) (Functor_cat B C)
  (@comp_cat_cov_func B (Product_cat C C) C Prod) (@Struct_sigma (Functor B C) (λ _ : τ (Functor B C), Functor B
  C) X Y)) Z (@one_cat_difference_cospan_transf B C C1 Prod t A T0 X Y Z f g))) x) (@fapp0 B C Z x)) (λ h : τ
  (@Transf B C (@kernel_adjunction_family_func B C (@additive_preadditive C Prod t A) t (@additive_terminal_object
  C Prod t A) P (@transf_arrow_diagram_func B C (@fapp0 (Functor_cat B (Product_cat C C)) (Functor_cat B C)
  (@comp_cat_cov_func B (Product_cat C C) C Prod) (@Struct_sigma (Functor B C) (λ _ : τ (Functor B C), Functor B
  C) X Y)) Z (@one_cat_difference_cospan_transf B C C1 Prod t A T0 X Y Z f g))) Z), (@tapp0_fapp0 B C
  (@kernel_adjunction_family_func B C (@additive_preadditive C Prod t A) t (@additive_terminal_object C Prod t A)
  P (@transf_arrow_diagram_func B C (@fapp0 (Functor_cat B (Product_cat C C)) (Functor_cat B C)
  (@comp_cat_cov_func B (Product_cat C C) C Prod) (@Struct_sigma (Functor B C) (λ _ : τ (Functor B C), Functor B
  C) X Y)) Z (@one_cat_difference_cospan_transf B C C1 Prod t A T0 X Y Z f g))) Z x h)) (@comp_fapp0 (Functor_cat
  B C) (@kernel_adjunction_family_func B C (@additive_preadditive C Prod t A) t (@additive_terminal_object C Prod
  t A) P (@transf_arrow_diagram_func B C (@fapp0 (Functor_cat B (Product_cat C C)) (Functor_cat B C)
  (@comp_cat_cov_func B (Product_cat C C) C Prod) (@Struct_sigma (Functor B C) (λ _ : τ (Functor B C), Functor B
  C) X Y)) Z (@one_cat_difference_cospan_transf B C C1 Prod t A T0 X Y Z f g))) X Z f
  (@one_cat_cospan_kernel_first B C C1 Prod t A T0 P Q X Y Z f g)) (@comp_fapp0 (Functor_cat B C)
  (@kernel_adjunction_family_func B C (@additive_preadditive C Prod t A) t (@additive_terminal_object C Prod t A)
  P (@transf_arrow_diagram_func B C (@fapp0 (Functor_cat B (Product_cat C C)) (Functor_cat B C)
  (@comp_cat_cov_func B (Product_cat C C) C Prod) (@Struct_sigma (Functor B C) (λ _ : τ (Functor B C), Functor B
  C) X Y)) Z (@one_cat_difference_cospan_transf B C C1 Prod t A T0 X Y Z f g))) Y Z g
  (@one_cat_cospan_kernel_second B C C1 Prod t A T0 P Q X Y Z f g)) (@one_cat_cospan_kernel_compatibility B C C1
  Prod t A T0 P Q X Y Z f g) : τ (@= (Hom C (@fapp0 B C (@kernel_adjunction_family_func B C (@additive_preadditive
  C Prod t A) t (@additive_terminal_object C Prod t A) P (@transf_arrow_diagram_func B C (@fapp0 (Functor_cat B
  (Product_cat C C)) (Functor_cat B C) (@comp_cat_cov_func B (Product_cat C C) C Prod) (@Struct_sigma (Functor B
  C) (λ _ : τ (Functor B C), Functor B C) X Y)) Z (@one_cat_difference_cospan_transf B C C1 Prod t A T0 X Y Z f
  g))) x) (@fapp0 B C Z x)) (@tapp0_fapp0 B C (@kernel_adjunction_family_func B C (@additive_preadditive C Prod t
  A) t (@additive_terminal_object C Prod t A) P (@transf_arrow_diagram_func B C (@fapp0 (Functor_cat B
  (Product_cat C C)) (Functor_cat B C) (@comp_cat_cov_func B (Product_cat C C) C Prod) (@Struct_sigma (Functor B
  C) (λ _ : τ (Functor B C), Functor B C) X Y)) Z (@one_cat_difference_cospan_transf B C C1 Prod t A T0 X Y Z f
  g))) Z x (@comp_fapp0 (Functor_cat B C) (@kernel_adjunction_family_func B C (@additive_preadditive C Prod t A) t
  (@additive_terminal_object C Prod t A) P (@transf_arrow_diagram_func B C (@fapp0 (Functor_cat B (Product_cat C
  C)) (Functor_cat B C) (@comp_cat_cov_func B (Product_cat C C) C Prod) (@Struct_sigma (Functor B C) (λ _ : τ
  (Functor B C), Functor B C) X Y)) Z (@one_cat_difference_cospan_transf B C C1 Prod t A T0 X Y Z f g))) X Z f
  (@one_cat_cospan_kernel_first B C C1 Prod t A T0 P Q X Y Z f g))) (@tapp0_fapp0 B C
  (@kernel_adjunction_family_func B C (@additive_preadditive C Prod t A) t (@additive_terminal_object C Prod t A)
  P (@transf_arrow_diagram_func B C (@fapp0 (Functor_cat B (Product_cat C C)) (Functor_cat B C)
  (@comp_cat_cov_func B (Product_cat C C) C Prod) (@Struct_sigma (Functor B C) (λ _ : τ (Functor B C), Functor B
  C) X Y)) Z (@one_cat_difference_cospan_transf B C C1 Prod t A T0 X Y Z f g))) Z x (@comp_fapp0 (Functor_cat B C)
  (@kernel_adjunction_family_func B C (@additive_preadditive C Prod t A) t (@additive_terminal_object C Prod t A)
  P (@transf_arrow_diagram_func B C (@fapp0 (Functor_cat B (Product_cat C C)) (Functor_cat B C)
  (@comp_cat_cov_func B (Product_cat C C) C Prod) (@Struct_sigma (Functor B C) (λ _ : τ (Functor B C), Functor B
  C) X Y)) Z (@one_cat_difference_cospan_transf B C C1 Prod t A T0 X Y Z f g))) Y Z g
  (@one_cat_cospan_kernel_second B C C1 Prod t A T0 P Q X Y Z f g))));

// A cover certifies the original Coim(r)→X factor.
assert [B C : Cat] (C1 : τ (IsNCat (cat_succ cat_zero) C)) [Prod : τ (Functor (Product_cat C C) C)] [t : τ (Obj
  C)] (A : τ (@AdditiveCategory C Prod t)) (T0 : τ (@TerminalObject (Op_cat C) t)) (P : τ
  (@KernelAdjunctionStructure C (@additive_preadditive C Prod t A) t (@additive_terminal_object C Prod t A))) (Q :
  τ (@CokernelAdjunctionStructure C (@additive_preadditive C Prod t A) t T0)) (N : τ (@OneCatAdjunctionNormality C
  (@additive_preadditive C Prod t A) C1 t (@additive_terminal_object C Prod t A) T0 P Q)) (X Y Z : τ (Functor B
  C)) (f : τ (@Transf B C X Z)) (g : τ (@Transf B C Y Z)) (zg : τ (@= (@Transf B C Z
  (@cokernel_adjunction_family_func B C (@additive_preadditive C Prod t A) t T0 Q (@transf_arrow_diagram_func B C
  Y Z g))) (@cokernel_adjunction_family_projection_transf B C (@additive_preadditive C Prod t A) t T0 Q
  (@transf_arrow_diagram_func B C Y Z g)) (@zero_arrow_family_zero_transf B C t (@additive_terminal_object C Prod
  t A) T0 Z (@cokernel_adjunction_family_func B C (@additive_preadditive C Prod t A) t T0 Q
  (@transf_arrow_diagram_func B C Y Z g))))) ⊢ @iso_evidence_to (Functor_cat B C) (@comp_cat_fapp0 B (Functor_cat
  WalkingArrow_cat C) C (@adjunction_coimage_func C (@additive_preadditive C Prod t A) t
  (@additive_terminal_object C Prod t A) T0 P Q) (@transf_arrow_diagram_func B C (@kernel_adjunction_family_func B
  C (@additive_preadditive C Prod t A) t (@additive_terminal_object C Prod t A) P (@transf_arrow_diagram_func B C
  (@fapp0 (Functor_cat B (Product_cat C C)) (Functor_cat B C) (@comp_cat_cov_func B (Product_cat C C) C Prod)
  (@Struct_sigma (Functor B C) (λ _ : τ (Functor B C), Functor B C) X Y)) Z (@one_cat_difference_cospan_transf B C
  C1 Prod t A T0 X Y Z f g))) X (@one_cat_cospan_kernel_first B C C1 Prod t A T0 P Q X Y Z f g))) X
  (@omega_equiv_along_iso_evidence (Functor_cat B C) (@comp_cat_fapp0 B (Functor_cat WalkingArrow_cat C) C
  (@adjunction_coimage_func C (@additive_preadditive C Prod t A) t (@additive_terminal_object C Prod t A) T0 P Q)
  (@transf_arrow_diagram_func B C (@kernel_adjunction_family_func B C (@additive_preadditive C Prod t A) t
  (@additive_terminal_object C Prod t A) P (@transf_arrow_diagram_func B C (@fapp0 (Functor_cat B (Product_cat C
  C)) (Functor_cat B C) (@comp_cat_cov_func B (Product_cat C C) C Prod) (@Struct_sigma (Functor B C) (λ _ : τ
  (Functor B C), Functor B C) X Y)) Z (@one_cat_difference_cospan_transf B C C1 Prod t A T0 X Y Z f g))) X
  (@one_cat_cospan_kernel_first B C C1 Prod t A T0 P Q X Y Z f g))) X (@fapp0 _ _ (@comp_cat_con_fapp1_func B
  (Functor_cat WalkingArrow_cat C) C (@transf_arrow_diagram_func B C (@kernel_adjunction_family_func B C
  (@additive_preadditive C Prod t A) t (@additive_terminal_object C Prod t A) P (@transf_arrow_diagram_func B C
  (@fapp0 (Functor_cat B (Product_cat C C)) (Functor_cat B C) (@comp_cat_cov_func B (Product_cat C C) C Prod)
  (@Struct_sigma (Functor B C) (λ _ : τ (Functor B C), Functor B C) X Y)) Z (@one_cat_difference_cospan_transf B C
  C1 Prod t A T0 X Y Z f g))) X (@one_cat_cospan_kernel_first B C C1 Prod t A T0 P Q X Y Z f g))
  (@adjunction_coimage_func C (@additive_preadditive C Prod t A) t (@additive_terminal_object C Prod t A) T0 P Q)
  (@diagram_evaluation_at_func WalkingArrow_cat C walking_arrow_tgt)) (@one_cat_adjunction_coimage_to_target C
  (@additive_preadditive C Prod t A) C1 t (@additive_terminal_object C Prod t A) T0 P Q))
  (@one_cat_cospan_kernel_first_cover B C C1 Prod t A T0 P Q N X Y Z f g zg)) ≡ (@fapp0 _ _
  (@comp_cat_con_fapp1_func B (Functor_cat WalkingArrow_cat C) C (@transf_arrow_diagram_func B C
  (@kernel_adjunction_family_func B C (@additive_preadditive C Prod t A) t (@additive_terminal_object C Prod t A)
  P (@transf_arrow_diagram_func B C (@fapp0 (Functor_cat B (Product_cat C C)) (Functor_cat B C)
  (@comp_cat_cov_func B (Product_cat C C) C Prod) (@Struct_sigma (Functor B C) (λ _ : τ (Functor B C), Functor B
  C) X Y)) Z (@one_cat_difference_cospan_transf B C C1 Prod t A T0 X Y Z f g))) X (@one_cat_cospan_kernel_first B
  C C1 Prod t A T0 P Q X Y Z f g)) (@adjunction_coimage_func C (@additive_preadditive C Prod t A) t
  (@additive_terminal_object C Prod t A) T0 P Q) (@diagram_evaluation_at_func WalkingArrow_cat C
  walking_arrow_tgt)) (@one_cat_adjunction_coimage_to_target C (@additive_preadditive C Prod t A) C1 t
  (@additive_terminal_object C Prod t A) T0 P Q));
assertnot [B C : Cat] (C1 : τ (IsNCat (cat_succ cat_zero) C)) [Prod : τ (Functor (Product_cat C C) C)] [t : τ (Obj
  C)] (A : τ (@AdditiveCategory C Prod t)) (T0 : τ (@TerminalObject (Op_cat C) t)) (P : τ
  (@KernelAdjunctionStructure C (@additive_preadditive C Prod t A) t (@additive_terminal_object C Prod t A))) (Q :
  τ (@CokernelAdjunctionStructure C (@additive_preadditive C Prod t A) t T0)) (N : τ (@OneCatAdjunctionNormality C
  (@additive_preadditive C Prod t A) C1 t (@additive_terminal_object C Prod t A) T0 P Q)) (X Y Z : τ (Functor B
  C)) (f : τ (@Transf B C X Z)) (g : τ (@Transf B C Y Z)) (zg : τ (@= (@Transf B C Z
  (@cokernel_adjunction_family_func B C (@additive_preadditive C Prod t A) t T0 Q (@transf_arrow_diagram_func B C
  Y Z g))) (@cokernel_adjunction_family_projection_transf B C (@additive_preadditive C Prod t A) t T0 Q
  (@transf_arrow_diagram_func B C Y Z g)) (@zero_arrow_family_zero_transf B C t (@additive_terminal_object C Prod
  t A) T0 Z (@cokernel_adjunction_family_func B C (@additive_preadditive C Prod t A) t T0 Q
  (@transf_arrow_diagram_func B C Y Z g))))) (other : τ (@Transf B C (@comp_cat_fapp0 B (Functor_cat
  WalkingArrow_cat C) C (@adjunction_coimage_func C (@additive_preadditive C Prod t A) t
  (@additive_terminal_object C Prod t A) T0 P Q) (@transf_arrow_diagram_func B C (@kernel_adjunction_family_func B
  C (@additive_preadditive C Prod t A) t (@additive_terminal_object C Prod t A) P (@transf_arrow_diagram_func B C
  (@fapp0 (Functor_cat B (Product_cat C C)) (Functor_cat B C) (@comp_cat_cov_func B (Product_cat C C) C Prod)
  (@Struct_sigma (Functor B C) (λ _ : τ (Functor B C), Functor B C) X Y)) Z (@one_cat_difference_cospan_transf B C
  C1 Prod t A T0 X Y Z f g))) X (@one_cat_cospan_kernel_first B C C1 Prod t A T0 P Q X Y Z f g))) X)) ⊢
  (@one_cat_cospan_kernel_first_cover B C C1 Prod t A T0 P Q N X Y Z f g zg) : τ (@OmegaEquivAlong (Functor_cat B
  C) (@comp_cat_fapp0 B (Functor_cat WalkingArrow_cat C) C (@adjunction_coimage_func C (@additive_preadditive C
  Prod t A) t (@additive_terminal_object C Prod t A) T0 P Q) (@transf_arrow_diagram_func B C
  (@kernel_adjunction_family_func B C (@additive_preadditive C Prod t A) t (@additive_terminal_object C Prod t A)
  P (@transf_arrow_diagram_func B C (@fapp0 (Functor_cat B (Product_cat C C)) (Functor_cat B C)
  (@comp_cat_cov_func B (Product_cat C C) C Prod) (@Struct_sigma (Functor B C) (λ _ : τ (Functor B C), Functor B
  C) X Y)) Z (@one_cat_difference_cospan_transf B C C1 Prod t A T0 X Y Z f g))) X (@one_cat_cospan_kernel_first B
  C C1 Prod t A T0 P Q X Y Z f g))) X other);
