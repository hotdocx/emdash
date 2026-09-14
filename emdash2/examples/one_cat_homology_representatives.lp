require open emdash.emdash3_2_one_cat_boundary_representatives;

// The cycle representative retains both the original class and the original homology quotient.
assert [B C : Cat] (C1 : τ (IsNCat (cat_succ cat_zero) C)) [Prod : τ (Functor (Product_cat C C) C)] [t : τ (Obj
  C)] (A : τ (@AdditiveCategory C Prod t)) (T0 : τ (@TerminalObject (Op_cat C) t)) (P : τ
  (@KernelAdjunctionStructure C (@additive_preadditive C Prod t A) t (@additive_terminal_object C Prod t A))) (Q :
  τ (@CokernelAdjunctionStructure C (@additive_preadditive C Prod t A) t T0)) (N : τ (@OneCatAdjunctionNormality C
  (@additive_preadditive C Prod t A) C1 t (@additive_terminal_object C Prod t A) T0 P Q)) (U : τ (Functor B C)) (D
  : τ (Functor B (Functor_cat WalkingArrow_cat C))) (h : τ (@Transf B (Functor_cat WalkingArrow_cat C)
  (@comp_cat_fapp0 B C (Functor_cat WalkingArrow_cat C) (@terminal_arrow_diagram_func C t
  (@additive_terminal_object C Prod t A)) U) D)) (X : τ (Functor B C)) (v : τ (@Transf B C X
  (@homology_adjunction_family_func B C (@additive_preadditive C Prod t A) t (@additive_terminal_object C Prod t
  A) T0 P Q U D h))) ⊢ (@one_cat_homology_representative_path B C C1 Prod t A T0 P Q N U D h X v) : τ (@= (@Transf
  B C (@kernel_adjunction_family_func B C (@additive_preadditive C Prod t A) t (@additive_terminal_object C Prod t
  A) P (@transf_arrow_diagram_func B C (@fapp0 (Functor_cat B (Product_cat C C)) (Functor_cat B C)
  (@comp_cat_cov_func B (Product_cat C C) C Prod) (@Struct_sigma (Functor B C) (λ _ : τ (Functor B C), Functor B
  C) X (@kernel_adjunction_family_func B C (@additive_preadditive C Prod t A) t (@additive_terminal_object C Prod
  t A) P D))) (@homology_adjunction_family_func B C (@additive_preadditive C Prod t A) t
  (@additive_terminal_object C Prod t A) T0 P Q U D h) (@one_cat_difference_cospan_transf B C C1 Prod t A T0 X
  (@kernel_adjunction_family_func B C (@additive_preadditive C Prod t A) t (@additive_terminal_object C Prod t A)
  P D) (@homology_adjunction_family_func B C (@additive_preadditive C Prod t A) t (@additive_terminal_object C
  Prod t A) T0 P Q U D h) v (@homology_adjunction_family_projection_transf B C (@additive_preadditive C Prod t A)
  t (@additive_terminal_object C Prod t A) T0 P Q U D h)))) (@homology_adjunction_family_func B C
  (@additive_preadditive C Prod t A) t (@additive_terminal_object C Prod t A) T0 P Q U D h)) (@comp_fapp0
  (Functor_cat B C) (@kernel_adjunction_family_func B C (@additive_preadditive C Prod t A) t
  (@additive_terminal_object C Prod t A) P (@transf_arrow_diagram_func B C (@fapp0 (Functor_cat B (Product_cat C
  C)) (Functor_cat B C) (@comp_cat_cov_func B (Product_cat C C) C Prod) (@Struct_sigma (Functor B C) (λ _ : τ
  (Functor B C), Functor B C) X (@kernel_adjunction_family_func B C (@additive_preadditive C Prod t A) t
  (@additive_terminal_object C Prod t A) P D))) (@homology_adjunction_family_func B C (@additive_preadditive C
  Prod t A) t (@additive_terminal_object C Prod t A) T0 P Q U D h) (@one_cat_difference_cospan_transf B C C1 Prod
  t A T0 X (@kernel_adjunction_family_func B C (@additive_preadditive C Prod t A) t (@additive_terminal_object C
  Prod t A) P D) (@homology_adjunction_family_func B C (@additive_preadditive C Prod t A) t
  (@additive_terminal_object C Prod t A) T0 P Q U D h) v (@homology_adjunction_family_projection_transf B C
  (@additive_preadditive C Prod t A) t (@additive_terminal_object C Prod t A) T0 P Q U D h)))) X
  (@homology_adjunction_family_func B C (@additive_preadditive C Prod t A) t (@additive_terminal_object C Prod t
  A) T0 P Q U D h) v (@one_cat_homology_representative_projection B C C1 Prod t A T0 P Q N U D h X v))
  (@comp_fapp0 (Functor_cat B C) (@kernel_adjunction_family_func B C (@additive_preadditive C Prod t A) t
  (@additive_terminal_object C Prod t A) P (@transf_arrow_diagram_func B C (@fapp0 (Functor_cat B (Product_cat C
  C)) (Functor_cat B C) (@comp_cat_cov_func B (Product_cat C C) C Prod) (@Struct_sigma (Functor B C) (λ _ : τ
  (Functor B C), Functor B C) X (@kernel_adjunction_family_func B C (@additive_preadditive C Prod t A) t
  (@additive_terminal_object C Prod t A) P D))) (@homology_adjunction_family_func B C (@additive_preadditive C
  Prod t A) t (@additive_terminal_object C Prod t A) T0 P Q U D h) (@one_cat_difference_cospan_transf B C C1 Prod
  t A T0 X (@kernel_adjunction_family_func B C (@additive_preadditive C Prod t A) t (@additive_terminal_object C
  Prod t A) P D) (@homology_adjunction_family_func B C (@additive_preadditive C Prod t A) t
  (@additive_terminal_object C Prod t A) T0 P Q U D h) v (@homology_adjunction_family_projection_transf B C
  (@additive_preadditive C Prod t A) t (@additive_terminal_object C Prod t A) T0 P Q U D h))))
  (@kernel_adjunction_family_func B C (@additive_preadditive C Prod t A) t (@additive_terminal_object C Prod t A)
  P D) (@homology_adjunction_family_func B C (@additive_preadditive C Prod t A) t (@additive_terminal_object C
  Prod t A) T0 P Q U D h) (@homology_adjunction_family_projection_transf B C (@additive_preadditive C Prod t A) t
  (@additive_terminal_object C Prod t A) T0 P Q U D h) (@one_cat_homology_representative_cycles B C C1 Prod t A T0
  P Q N U D h X v)));
assert [B C : Cat] (C1 : τ (IsNCat (cat_succ cat_zero) C)) [Prod : τ (Functor (Product_cat C C) C)] [t : τ (Obj
  C)] (A : τ (@AdditiveCategory C Prod t)) (T0 : τ (@TerminalObject (Op_cat C) t)) (P : τ
  (@KernelAdjunctionStructure C (@additive_preadditive C Prod t A) t (@additive_terminal_object C Prod t A))) (Q :
  τ (@CokernelAdjunctionStructure C (@additive_preadditive C Prod t A) t T0)) (N : τ (@OneCatAdjunctionNormality C
  (@additive_preadditive C Prod t A) C1 t (@additive_terminal_object C Prod t A) T0 P Q)) (U : τ (Functor B C)) (D
  : τ (Functor B (Functor_cat WalkingArrow_cat C))) (h : τ (@Transf B (Functor_cat WalkingArrow_cat C)
  (@comp_cat_fapp0 B C (Functor_cat WalkingArrow_cat C) (@terminal_arrow_diagram_func C t
  (@additive_terminal_object C Prod t A)) U) D)) (X : τ (Functor B C)) (v : τ (@Transf B C X
  (@homology_adjunction_family_func B C (@additive_preadditive C Prod t A) t (@additive_terminal_object C Prod t
  A) T0 P Q U D h))) ⊢ @iso_evidence_to (Functor_cat B C) (@comp_cat_fapp0 B (Functor_cat WalkingArrow_cat C) C
  (@adjunction_coimage_func C (@additive_preadditive C Prod t A) t (@additive_terminal_object C Prod t A) T0 P Q)
  (@transf_arrow_diagram_func B C (@kernel_adjunction_family_func B C (@additive_preadditive C Prod t A) t
  (@additive_terminal_object C Prod t A) P (@transf_arrow_diagram_func B C (@fapp0 (Functor_cat B (Product_cat C
  C)) (Functor_cat B C) (@comp_cat_cov_func B (Product_cat C C) C Prod) (@Struct_sigma (Functor B C) (λ _ : τ
  (Functor B C), Functor B C) X (@kernel_adjunction_family_func B C (@additive_preadditive C Prod t A) t
  (@additive_terminal_object C Prod t A) P D))) (@homology_adjunction_family_func B C (@additive_preadditive C
  Prod t A) t (@additive_terminal_object C Prod t A) T0 P Q U D h) (@one_cat_difference_cospan_transf B C C1 Prod
  t A T0 X (@kernel_adjunction_family_func B C (@additive_preadditive C Prod t A) t (@additive_terminal_object C
  Prod t A) P D) (@homology_adjunction_family_func B C (@additive_preadditive C Prod t A) t
  (@additive_terminal_object C Prod t A) T0 P Q U D h) v (@homology_adjunction_family_projection_transf B C
  (@additive_preadditive C Prod t A) t (@additive_terminal_object C Prod t A) T0 P Q U D h)))) X
  (@one_cat_homology_representative_projection B C C1 Prod t A T0 P Q N U D h X v))) X
  (@omega_equiv_along_iso_evidence (Functor_cat B C) (@comp_cat_fapp0 B (Functor_cat WalkingArrow_cat C) C
  (@adjunction_coimage_func C (@additive_preadditive C Prod t A) t (@additive_terminal_object C Prod t A) T0 P Q)
  (@transf_arrow_diagram_func B C (@kernel_adjunction_family_func B C (@additive_preadditive C Prod t A) t
  (@additive_terminal_object C Prod t A) P (@transf_arrow_diagram_func B C (@fapp0 (Functor_cat B (Product_cat C
  C)) (Functor_cat B C) (@comp_cat_cov_func B (Product_cat C C) C Prod) (@Struct_sigma (Functor B C) (λ _ : τ
  (Functor B C), Functor B C) X (@kernel_adjunction_family_func B C (@additive_preadditive C Prod t A) t
  (@additive_terminal_object C Prod t A) P D))) (@homology_adjunction_family_func B C (@additive_preadditive C
  Prod t A) t (@additive_terminal_object C Prod t A) T0 P Q U D h) (@one_cat_difference_cospan_transf B C C1 Prod
  t A T0 X (@kernel_adjunction_family_func B C (@additive_preadditive C Prod t A) t (@additive_terminal_object C
  Prod t A) P D) (@homology_adjunction_family_func B C (@additive_preadditive C Prod t A) t
  (@additive_terminal_object C Prod t A) T0 P Q U D h) v (@homology_adjunction_family_projection_transf B C
  (@additive_preadditive C Prod t A) t (@additive_terminal_object C Prod t A) T0 P Q U D h)))) X
  (@one_cat_homology_representative_projection B C C1 Prod t A T0 P Q N U D h X v))) X (@fapp0 _ _
  (@comp_cat_con_fapp1_func B (Functor_cat WalkingArrow_cat C) C (@transf_arrow_diagram_func B C
  (@kernel_adjunction_family_func B C (@additive_preadditive C Prod t A) t (@additive_terminal_object C Prod t A)
  P (@transf_arrow_diagram_func B C (@fapp0 (Functor_cat B (Product_cat C C)) (Functor_cat B C)
  (@comp_cat_cov_func B (Product_cat C C) C Prod) (@Struct_sigma (Functor B C) (λ _ : τ (Functor B C), Functor B
  C) X (@kernel_adjunction_family_func B C (@additive_preadditive C Prod t A) t (@additive_terminal_object C Prod
  t A) P D))) (@homology_adjunction_family_func B C (@additive_preadditive C Prod t A) t
  (@additive_terminal_object C Prod t A) T0 P Q U D h) (@one_cat_difference_cospan_transf B C C1 Prod t A T0 X
  (@kernel_adjunction_family_func B C (@additive_preadditive C Prod t A) t (@additive_terminal_object C Prod t A)
  P D) (@homology_adjunction_family_func B C (@additive_preadditive C Prod t A) t (@additive_terminal_object C
  Prod t A) T0 P Q U D h) v (@homology_adjunction_family_projection_transf B C (@additive_preadditive C Prod t A)
  t (@additive_terminal_object C Prod t A) T0 P Q U D h)))) X (@one_cat_homology_representative_projection B C C1
  Prod t A T0 P Q N U D h X v)) (@adjunction_coimage_func C (@additive_preadditive C Prod t A) t
  (@additive_terminal_object C Prod t A) T0 P Q) (@diagram_evaluation_at_func WalkingArrow_cat C
  walking_arrow_tgt)) (@one_cat_adjunction_coimage_to_target C (@additive_preadditive C Prod t A) C1 t
  (@additive_terminal_object C Prod t A) T0 P Q)) (@one_cat_homology_representative_cover B C C1 Prod t A T0 P Q N
  U D h X v)) ≡ (@fapp0 _ _ (@comp_cat_con_fapp1_func B (Functor_cat WalkingArrow_cat C) C
  (@transf_arrow_diagram_func B C (@kernel_adjunction_family_func B C (@additive_preadditive C Prod t A) t
  (@additive_terminal_object C Prod t A) P (@transf_arrow_diagram_func B C (@fapp0 (Functor_cat B (Product_cat C
  C)) (Functor_cat B C) (@comp_cat_cov_func B (Product_cat C C) C Prod) (@Struct_sigma (Functor B C) (λ _ : τ
  (Functor B C), Functor B C) X (@kernel_adjunction_family_func B C (@additive_preadditive C Prod t A) t
  (@additive_terminal_object C Prod t A) P D))) (@homology_adjunction_family_func B C (@additive_preadditive C
  Prod t A) t (@additive_terminal_object C Prod t A) T0 P Q U D h) (@one_cat_difference_cospan_transf B C C1 Prod
  t A T0 X (@kernel_adjunction_family_func B C (@additive_preadditive C Prod t A) t (@additive_terminal_object C
  Prod t A) P D) (@homology_adjunction_family_func B C (@additive_preadditive C Prod t A) t
  (@additive_terminal_object C Prod t A) T0 P Q U D h) v (@homology_adjunction_family_projection_transf B C
  (@additive_preadditive C Prod t A) t (@additive_terminal_object C Prod t A) T0 P Q U D h)))) X
  (@one_cat_homology_representative_projection B C C1 Prod t A T0 P Q N U D h X v)) (@adjunction_coimage_func C
  (@additive_preadditive C Prod t A) t (@additive_terminal_object C Prod t A) T0 P Q) (@diagram_evaluation_at_func
  WalkingArrow_cat C walking_arrow_tgt)) (@one_cat_adjunction_coimage_to_target C (@additive_preadditive C Prod t
  A) C1 t (@additive_terminal_object C Prod t A) T0 P Q));

// The original boundary reconstructs the same cycle after its derived cover.
assert [B C : Cat] (C1 : τ (IsNCat (cat_succ cat_zero) C)) [Prod : τ (Functor (Product_cat C C) C)] [t : τ (Obj
  C)] (A : τ (@AdditiveCategory C Prod t)) (T0 : τ (@TerminalObject (Op_cat C) t)) (P : τ
  (@KernelAdjunctionStructure C (@additive_preadditive C Prod t A) t (@additive_terminal_object C Prod t A))) (Q :
  τ (@CokernelAdjunctionStructure C (@additive_preadditive C Prod t A) t T0)) (N : τ (@OneCatAdjunctionNormality C
  (@additive_preadditive C Prod t A) C1 t (@additive_terminal_object C Prod t A) T0 P Q)) (U : τ (Functor B C)) (D
  : τ (Functor B (Functor_cat WalkingArrow_cat C))) (h : τ (@Transf B (Functor_cat WalkingArrow_cat C)
  (@comp_cat_fapp0 B C (Functor_cat WalkingArrow_cat C) (@terminal_arrow_diagram_func C t
  (@additive_terminal_object C Prod t A)) U) D)) (X : τ (Functor B C)) (v : τ (@Transf B C X
  (@kernel_adjunction_family_func B C (@additive_preadditive C Prod t A) t (@additive_terminal_object C Prod t A)
  P D))) (z : τ (@= (@Transf B C X (@homology_adjunction_family_func B C (@additive_preadditive C Prod t A) t
  (@additive_terminal_object C Prod t A) T0 P Q U D h)) (@comp_fapp0 (Functor_cat B C) X
  (@kernel_adjunction_family_func B C (@additive_preadditive C Prod t A) t (@additive_terminal_object C Prod t A)
  P D) (@homology_adjunction_family_func B C (@additive_preadditive C Prod t A) t (@additive_terminal_object C
  Prod t A) T0 P Q U D h) (@homology_adjunction_family_projection_transf B C (@additive_preadditive C Prod t A) t
  (@additive_terminal_object C Prod t A) T0 P Q U D h) v) (@zero_arrow_family_zero_transf B C t
  (@additive_terminal_object C Prod t A) T0 X (@homology_adjunction_family_func B C (@additive_preadditive C Prod
  t A) t (@additive_terminal_object C Prod t A) T0 P Q U D h)))) ⊢ (@one_cat_boundary_representative_path B C C1
  Prod t A T0 P Q N U D h X v z) : τ (@= (@Transf B C (@kernel_adjunction_family_func B C (@additive_preadditive C
  Prod t A) t (@additive_terminal_object C Prod t A) P (@transf_arrow_diagram_func B C (@fapp0 (Functor_cat B
  (Product_cat C C)) (Functor_cat B C) (@comp_cat_cov_func B (Product_cat C C) C Prod) (@Struct_sigma (Functor B
  C) (λ _ : τ (Functor B C), Functor B C) X U)) (@comp_cat_fapp0 B (Functor_cat WalkingArrow_cat C) C
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
  Prod t A) P U D h) (@one_cat_boundary_representative_map B C C1 Prod t A T0 P Q N U D h X v z)) (@comp_fapp0
  (Functor_cat B C) (@kernel_adjunction_family_func B C (@additive_preadditive C Prod t A) t
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
  (@one_cat_boundary_representative_projection B C C1 Prod t A T0 P Q N U D h X v z)));

// The coimage lift keeps the original normality inverse and original image lift.
assert [B C : Cat] (C1 : τ (IsNCat (cat_succ cat_zero) C)) [Prod : τ (Functor (Product_cat C C) C)] [t : τ (Obj
  C)] (A : τ (@AdditiveCategory C Prod t)) (T0 : τ (@TerminalObject (Op_cat C) t)) (P : τ
  (@KernelAdjunctionStructure C (@additive_preadditive C Prod t A) t (@additive_terminal_object C Prod t A))) (Q :
  τ (@CokernelAdjunctionStructure C (@additive_preadditive C Prod t A) t T0)) (N : τ (@OneCatAdjunctionNormality C
  (@additive_preadditive C Prod t A) C1 t (@additive_terminal_object C Prod t A) T0 P Q)) (U : τ (Functor B C)) (D
  : τ (Functor B (Functor_cat WalkingArrow_cat C))) (h : τ (@Transf B (Functor_cat WalkingArrow_cat C)
  (@comp_cat_fapp0 B C (Functor_cat WalkingArrow_cat C) (@terminal_arrow_diagram_func C t
  (@additive_terminal_object C Prod t A)) U) D)) (X : τ (Functor B C)) (v : τ (@Transf B C X
  (@kernel_adjunction_family_func B C (@additive_preadditive C Prod t A) t (@additive_terminal_object C Prod t A)
  P D))) (z : τ (@= (@Transf B C X (@homology_adjunction_family_func B C (@additive_preadditive C Prod t A) t
  (@additive_terminal_object C Prod t A) T0 P Q U D h)) (@comp_fapp0 (Functor_cat B C) X
  (@kernel_adjunction_family_func B C (@additive_preadditive C Prod t A) t (@additive_terminal_object C Prod t A)
  P D) (@homology_adjunction_family_func B C (@additive_preadditive C Prod t A) t (@additive_terminal_object C
  Prod t A) T0 P Q U D h) (@homology_adjunction_family_projection_transf B C (@additive_preadditive C Prod t A) t
  (@additive_terminal_object C Prod t A) T0 P Q U D h) v) (@zero_arrow_family_zero_transf B C t
  (@additive_terminal_object C Prod t A) T0 X (@homology_adjunction_family_func B C (@additive_preadditive C Prod
  t A) t (@additive_terminal_object C Prod t A) T0 P Q U D h)))) ⊢ (@one_cat_boundary_coimage_lift B C C1 Prod t A
  T0 P Q N U D h X v z) ≡ (@comp_fapp0 (Functor_cat B C) X (@comp_cat_fapp0 B (Functor_cat WalkingArrow_cat C) C
  (@adjunction_image_func C (@additive_preadditive C Prod t A) t (@additive_terminal_object C Prod t A) T0 P Q)
  (@kernel_adjunction_family_boundary_diagram_func B C (@additive_preadditive C Prod t A) t
  (@additive_terminal_object C Prod t A) P U D h)) (@comp_cat_fapp0 B (Functor_cat WalkingArrow_cat C) C
  (@adjunction_coimage_func C (@additive_preadditive C Prod t A) t (@additive_terminal_object C Prod t A) T0 P Q)
  (@kernel_adjunction_family_boundary_diagram_func B C (@additive_preadditive C Prod t A) t
  (@additive_terminal_object C Prod t A) P U D h)) (@fapp0 _ _ (@comp_cat_con_fapp1_func B (Functor_cat
  WalkingArrow_cat C) C (@kernel_adjunction_family_boundary_diagram_func B C (@additive_preadditive C Prod t A) t
  (@additive_terminal_object C Prod t A) P U D h) (@adjunction_image_func C (@additive_preadditive C Prod t A) t
  (@additive_terminal_object C Prod t A) T0 P Q) (@adjunction_coimage_func C (@additive_preadditive C Prod t A) t
  (@additive_terminal_object C Prod t A) T0 P Q)) (@one_cat_coimage_image_inverse_transf C (@additive_preadditive
  C Prod t A) C1 t (@additive_terminal_object C Prod t A) T0 P Q N)) (@one_cat_boundary_image_lift B C C1 Prod t A
  T0 P Q N U D h X v z));
assertnot [B C : Cat] (C1 : τ (IsNCat (cat_succ cat_zero) C)) [Prod : τ (Functor (Product_cat C C) C)] [t : τ (Obj
  C)] (A : τ (@AdditiveCategory C Prod t)) (T0 : τ (@TerminalObject (Op_cat C) t)) (P : τ
  (@KernelAdjunctionStructure C (@additive_preadditive C Prod t A) t (@additive_terminal_object C Prod t A))) (Q :
  τ (@CokernelAdjunctionStructure C (@additive_preadditive C Prod t A) t T0)) (N : τ (@OneCatAdjunctionNormality C
  (@additive_preadditive C Prod t A) C1 t (@additive_terminal_object C Prod t A) T0 P Q)) (U : τ (Functor B C)) (D
  : τ (Functor B (Functor_cat WalkingArrow_cat C))) (h : τ (@Transf B (Functor_cat WalkingArrow_cat C)
  (@comp_cat_fapp0 B C (Functor_cat WalkingArrow_cat C) (@terminal_arrow_diagram_func C t
  (@additive_terminal_object C Prod t A)) U) D)) (X : τ (Functor B C)) (v : τ (@Transf B C X
  (@kernel_adjunction_family_func B C (@additive_preadditive C Prod t A) t (@additive_terminal_object C Prod t A)
  P D))) (z : τ (@= (@Transf B C X (@homology_adjunction_family_func B C (@additive_preadditive C Prod t A) t
  (@additive_terminal_object C Prod t A) T0 P Q U D h)) (@comp_fapp0 (Functor_cat B C) X
  (@kernel_adjunction_family_func B C (@additive_preadditive C Prod t A) t (@additive_terminal_object C Prod t A)
  P D) (@homology_adjunction_family_func B C (@additive_preadditive C Prod t A) t (@additive_terminal_object C
  Prod t A) T0 P Q U D h) (@homology_adjunction_family_projection_transf B C (@additive_preadditive C Prod t A) t
  (@additive_terminal_object C Prod t A) T0 P Q U D h) v) (@zero_arrow_family_zero_transf B C t
  (@additive_terminal_object C Prod t A) T0 X (@homology_adjunction_family_func B C (@additive_preadditive C Prod
  t A) t (@additive_terminal_object C Prod t A) T0 P Q U D h)))) (other : τ (@Transf B C
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
  (@additive_terminal_object C Prod t A) P U D h)))))) (@kernel_adjunction_family_func B C (@additive_preadditive
  C Prod t A) t (@additive_terminal_object C Prod t A) P D))) ⊢ (@one_cat_boundary_representative_path B C C1 Prod
  t A T0 P Q N U D h X v z) : τ (@= (@Transf B C (@kernel_adjunction_family_func B C (@additive_preadditive C Prod
  t A) t (@additive_terminal_object C Prod t A) P (@transf_arrow_diagram_func B C (@fapp0 (Functor_cat B
  (Product_cat C C)) (Functor_cat B C) (@comp_cat_cov_func B (Product_cat C C) C Prod) (@Struct_sigma (Functor B
  C) (λ _ : τ (Functor B C), Functor B C) X U)) (@comp_cat_fapp0 B (Functor_cat WalkingArrow_cat C) C
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
  C Prod t A) t (@additive_terminal_object C Prod t A) P D)) other (@comp_fapp0 (Functor_cat B C)
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
  (@additive_terminal_object C Prod t A) P U D h)))))) X (@kernel_adjunction_family_func B C
  (@additive_preadditive C Prod t A) t (@additive_terminal_object C Prod t A) P D) v
  (@one_cat_boundary_representative_projection B C C1 Prod t A T0 P Q N U D h X v z)));
