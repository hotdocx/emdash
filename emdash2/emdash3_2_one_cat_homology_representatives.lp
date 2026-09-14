/* Whole cycle representatives after a derived categorical cover. */
require open emdash.emdash3_2_one_cat_cospan_kernel_covers;
require open emdash.emdash3_2_one_cat_quotient_cokernel_zero;
require open emdash.emdash3_2_one_cat_homology_cover_maps;

// The original difference kernel is a whole parameter object for representatives of v.
symbol one_cat_homology_representative_func [B C : Cat] (C1 : τ (IsNCat (cat_succ cat_zero) C)) [Prod : τ
  (Functor (Product_cat C C) C)] [t : τ (Obj C)] (A : τ (@AdditiveCategory C Prod t)) (T0 : τ (@TerminalObject
  (Op_cat C) t)) (P : τ (@KernelAdjunctionStructure C (@additive_preadditive C Prod t A) t
  (@additive_terminal_object C Prod t A))) (Q : τ (@CokernelAdjunctionStructure C (@additive_preadditive C Prod t
  A) t T0)) (N : τ (@OneCatAdjunctionNormality C (@additive_preadditive C Prod t A) C1 t
  (@additive_terminal_object C Prod t A) T0 P Q)) (U : τ (Functor B C)) (D : τ (Functor B (Functor_cat
  WalkingArrow_cat C))) (h : τ (@Transf B (Functor_cat WalkingArrow_cat C) (@comp_cat_fapp0 B C (Functor_cat
  WalkingArrow_cat C) (@terminal_arrow_diagram_func C t (@additive_terminal_object C Prod t A)) U) D)) (X : τ
  (Functor B C)) (v : τ (@Transf B C X (@homology_adjunction_family_func B C (@additive_preadditive C Prod t A) t
  (@additive_terminal_object C Prod t A) T0 P Q U D h)))
 : τ (Functor B C)
≔ (@kernel_adjunction_family_func B C (@additive_preadditive C Prod t A) t (@additive_terminal_object C Prod t A)
  P (@transf_arrow_diagram_func B C (@fapp0 (Functor_cat B (Product_cat C C)) (Functor_cat B C)
  (@comp_cat_cov_func B (Product_cat C C) C Prod) (@Struct_sigma (Functor B C) (λ _ : τ (Functor B C), Functor B
  C) X (@kernel_adjunction_family_func B C (@additive_preadditive C Prod t A) t (@additive_terminal_object C Prod
  t A) P D))) (@homology_adjunction_family_func B C (@additive_preadditive C Prod t A) t
  (@additive_terminal_object C Prod t A) T0 P Q U D h) (@one_cat_difference_cospan_transf B C C1 Prod t A T0 X
  (@kernel_adjunction_family_func B C (@additive_preadditive C Prod t A) t (@additive_terminal_object C Prod t A)
  P D) (@homology_adjunction_family_func B C (@additive_preadditive C Prod t A) t (@additive_terminal_object C
  Prod t A) T0 P Q U D h) v (@homology_adjunction_family_projection_transf B C (@additive_preadditive C Prod t A)
  t (@additive_terminal_object C Prod t A) T0 P Q U D h))));

// The original first projection covers the original source of v.
symbol one_cat_homology_representative_projection [B C : Cat] (C1 : τ (IsNCat (cat_succ cat_zero) C)) [Prod
  : τ (Functor (Product_cat C C) C)] [t : τ (Obj C)] (A : τ (@AdditiveCategory C Prod t)) (T0 : τ (@TerminalObject
  (Op_cat C) t)) (P : τ (@KernelAdjunctionStructure C (@additive_preadditive C Prod t A) t
  (@additive_terminal_object C Prod t A))) (Q : τ (@CokernelAdjunctionStructure C (@additive_preadditive C Prod t
  A) t T0)) (N : τ (@OneCatAdjunctionNormality C (@additive_preadditive C Prod t A) C1 t
  (@additive_terminal_object C Prod t A) T0 P Q)) (U : τ (Functor B C)) (D : τ (Functor B (Functor_cat
  WalkingArrow_cat C))) (h : τ (@Transf B (Functor_cat WalkingArrow_cat C) (@comp_cat_fapp0 B C (Functor_cat
  WalkingArrow_cat C) (@terminal_arrow_diagram_func C t (@additive_terminal_object C Prod t A)) U) D)) (X : τ
  (Functor B C)) (v : τ (@Transf B C X (@homology_adjunction_family_func B C (@additive_preadditive C Prod t A) t
  (@additive_terminal_object C Prod t A) T0 P Q U D h)))
 : τ (@Transf B C (@kernel_adjunction_family_func B C (@additive_preadditive C Prod t A) t
  (@additive_terminal_object C Prod t A) P (@transf_arrow_diagram_func B C (@fapp0 (Functor_cat B (Product_cat C
  C)) (Functor_cat B C) (@comp_cat_cov_func B (Product_cat C C) C Prod) (@Struct_sigma (Functor B C) (λ _ : τ
  (Functor B C), Functor B C) X (@kernel_adjunction_family_func B C (@additive_preadditive C Prod t A) t
  (@additive_terminal_object C Prod t A) P D))) (@homology_adjunction_family_func B C (@additive_preadditive C
  Prod t A) t (@additive_terminal_object C Prod t A) T0 P Q U D h) (@one_cat_difference_cospan_transf B C C1 Prod
  t A T0 X (@kernel_adjunction_family_func B C (@additive_preadditive C Prod t A) t (@additive_terminal_object C
  Prod t A) P D) (@homology_adjunction_family_func B C (@additive_preadditive C Prod t A) t
  (@additive_terminal_object C Prod t A) T0 P Q U D h) v (@homology_adjunction_family_projection_transf B C
  (@additive_preadditive C Prod t A) t (@additive_terminal_object C Prod t A) T0 P Q U D h)))) X)
≔ @one_cat_cospan_kernel_first B C C1 Prod t A T0 P Q X (@kernel_adjunction_family_func B C
  (@additive_preadditive C Prod t A) t (@additive_terminal_object C Prod t A) P D)
  (@homology_adjunction_family_func B C (@additive_preadditive C Prod t A) t (@additive_terminal_object C Prod t
  A) T0 P Q U D h) v (@homology_adjunction_family_projection_transf B C (@additive_preadditive C Prod t A) t
  (@additive_terminal_object C Prod t A) T0 P Q U D h);

// The original second projection is a whole map to the original cycle object.
symbol one_cat_homology_representative_cycles [B C : Cat] (C1 : τ (IsNCat (cat_succ cat_zero) C)) [Prod : τ
  (Functor (Product_cat C C) C)] [t : τ (Obj C)] (A : τ (@AdditiveCategory C Prod t)) (T0 : τ (@TerminalObject
  (Op_cat C) t)) (P : τ (@KernelAdjunctionStructure C (@additive_preadditive C Prod t A) t
  (@additive_terminal_object C Prod t A))) (Q : τ (@CokernelAdjunctionStructure C (@additive_preadditive C Prod t
  A) t T0)) (N : τ (@OneCatAdjunctionNormality C (@additive_preadditive C Prod t A) C1 t
  (@additive_terminal_object C Prod t A) T0 P Q)) (U : τ (Functor B C)) (D : τ (Functor B (Functor_cat
  WalkingArrow_cat C))) (h : τ (@Transf B (Functor_cat WalkingArrow_cat C) (@comp_cat_fapp0 B C (Functor_cat
  WalkingArrow_cat C) (@terminal_arrow_diagram_func C t (@additive_terminal_object C Prod t A)) U) D)) (X : τ
  (Functor B C)) (v : τ (@Transf B C X (@homology_adjunction_family_func B C (@additive_preadditive C Prod t A) t
  (@additive_terminal_object C Prod t A) T0 P Q U D h)))
 : τ (@Transf B C (@kernel_adjunction_family_func B C (@additive_preadditive C Prod t A) t
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
  P D))
≔ @one_cat_cospan_kernel_second B C C1 Prod t A T0 P Q X (@kernel_adjunction_family_func B C
  (@additive_preadditive C Prod t A) t (@additive_terminal_object C Prod t A) P D)
  (@homology_adjunction_family_func B C (@additive_preadditive C Prod t A) t (@additive_terminal_object C Prod t
  A) T0 P Q U D h) v (@homology_adjunction_family_projection_transf B C (@additive_preadditive C Prod t A) t
  (@additive_terminal_object C Prod t A) T0 P Q U D h);

// The original homology quotient reconstructs v after the derived cover.
symbol one_cat_homology_representative_path [B C : Cat] (C1 : τ (IsNCat (cat_succ cat_zero) C)) [Prod : τ
  (Functor (Product_cat C C) C)] [t : τ (Obj C)] (A : τ (@AdditiveCategory C Prod t)) (T0 : τ (@TerminalObject
  (Op_cat C) t)) (P : τ (@KernelAdjunctionStructure C (@additive_preadditive C Prod t A) t
  (@additive_terminal_object C Prod t A))) (Q : τ (@CokernelAdjunctionStructure C (@additive_preadditive C Prod t
  A) t T0)) (N : τ (@OneCatAdjunctionNormality C (@additive_preadditive C Prod t A) C1 t
  (@additive_terminal_object C Prod t A) T0 P Q)) (U : τ (Functor B C)) (D : τ (Functor B (Functor_cat
  WalkingArrow_cat C))) (h : τ (@Transf B (Functor_cat WalkingArrow_cat C) (@comp_cat_fapp0 B C (Functor_cat
  WalkingArrow_cat C) (@terminal_arrow_diagram_func C t (@additive_terminal_object C Prod t A)) U) D)) (X : τ
  (Functor B C)) (v : τ (@Transf B C X (@homology_adjunction_family_func B C (@additive_preadditive C Prod t A) t
  (@additive_terminal_object C Prod t A) T0 P Q U D h)))
 : τ (@= (@Transf B C (@kernel_adjunction_family_func B C (@additive_preadditive C Prod t A) t
  (@additive_terminal_object C Prod t A) P (@transf_arrow_diagram_func B C (@fapp0 (Functor_cat B (Product_cat C
  C)) (Functor_cat B C) (@comp_cat_cov_func B (Product_cat C C) C Prod) (@Struct_sigma (Functor B C) (λ _ : τ
  (Functor B C), Functor B C) X (@kernel_adjunction_family_func B C (@additive_preadditive C Prod t A) t
  (@additive_terminal_object C Prod t A) P D))) (@homology_adjunction_family_func B C (@additive_preadditive C
  Prod t A) t (@additive_terminal_object C Prod t A) T0 P Q U D h) (@one_cat_difference_cospan_transf B C C1 Prod
  t A T0 X (@kernel_adjunction_family_func B C (@additive_preadditive C Prod t A) t (@additive_terminal_object C
  Prod t A) P D) (@homology_adjunction_family_func B C (@additive_preadditive C Prod t A) t
  (@additive_terminal_object C Prod t A) T0 P Q U D h) v (@homology_adjunction_family_projection_transf B C
  (@additive_preadditive C Prod t A) t (@additive_terminal_object C Prod t A) T0 P Q U D h))))
  (@homology_adjunction_family_func B C (@additive_preadditive C Prod t A) t (@additive_terminal_object C Prod t
  A) T0 P Q U D h)) (@comp_fapp0 (Functor_cat B C) (@kernel_adjunction_family_func B C (@additive_preadditive C
  Prod t A) t (@additive_terminal_object C Prod t A) P (@transf_arrow_diagram_func B C (@fapp0 (Functor_cat B
  (Product_cat C C)) (Functor_cat B C) (@comp_cat_cov_func B (Product_cat C C) C Prod) (@Struct_sigma (Functor B
  C) (λ _ : τ (Functor B C), Functor B C) X (@kernel_adjunction_family_func B C (@additive_preadditive C Prod t A)
  t (@additive_terminal_object C Prod t A) P D))) (@homology_adjunction_family_func B C (@additive_preadditive C
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
  (@additive_terminal_object C Prod t A) T0 P Q U D h) (@one_cat_homology_representative_cycles B C C1 Prod
  t A T0 P Q N U D h X v)))
≔ @one_cat_cospan_kernel_compatibility B C C1 Prod t A T0 P Q X (@kernel_adjunction_family_func B C
  (@additive_preadditive C Prod t A) t (@additive_terminal_object C Prod t A) P D)
  (@homology_adjunction_family_func B C (@additive_preadditive C Prod t A) t (@additive_terminal_object C Prod t
  A) T0 P Q U D h) v (@homology_adjunction_family_projection_transf B C (@additive_preadditive C Prod t A) t
  (@additive_terminal_object C Prod t A) T0 P Q U D h);

// The representative projection has a derived categorical cover, with no supplied cover input.
symbol one_cat_homology_representative_cover [B C : Cat] (C1 : τ (IsNCat (cat_succ cat_zero) C)) [Prod : τ
  (Functor (Product_cat C C) C)] [t : τ (Obj C)] (A : τ (@AdditiveCategory C Prod t)) (T0 : τ (@TerminalObject
  (Op_cat C) t)) (P : τ (@KernelAdjunctionStructure C (@additive_preadditive C Prod t A) t
  (@additive_terminal_object C Prod t A))) (Q : τ (@CokernelAdjunctionStructure C (@additive_preadditive C Prod t
  A) t T0)) (N : τ (@OneCatAdjunctionNormality C (@additive_preadditive C Prod t A) C1 t
  (@additive_terminal_object C Prod t A) T0 P Q)) (U : τ (Functor B C)) (D : τ (Functor B (Functor_cat
  WalkingArrow_cat C))) (h : τ (@Transf B (Functor_cat WalkingArrow_cat C) (@comp_cat_fapp0 B C (Functor_cat
  WalkingArrow_cat C) (@terminal_arrow_diagram_func C t (@additive_terminal_object C Prod t A)) U) D)) (X : τ
  (Functor B C)) (v : τ (@Transf B C X (@homology_adjunction_family_func B C (@additive_preadditive C Prod t A) t
  (@additive_terminal_object C Prod t A) T0 P Q U D h)))
 : τ (@OmegaEquivAlong (Functor_cat B C) (@comp_cat_fapp0 B (Functor_cat WalkingArrow_cat C) C
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
  t (@additive_terminal_object C Prod t A) T0 P Q U D h)))) X (@one_cat_homology_representative_projection B
  C C1 Prod t A T0 P Q N U D h X v)) (@adjunction_coimage_func C (@additive_preadditive C Prod t A) t
  (@additive_terminal_object C Prod t A) T0 P Q) (@diagram_evaluation_at_func WalkingArrow_cat C
  walking_arrow_tgt)) (@one_cat_adjunction_coimage_to_target C (@additive_preadditive C Prod t A) C1 t
  (@additive_terminal_object C Prod t A) T0 P Q)))
≔ @one_cat_cospan_kernel_first_cover B C C1 Prod t A T0 P Q N X (@kernel_adjunction_family_func B C
  (@additive_preadditive C Prod t A) t (@additive_terminal_object C Prod t A) P D)
  (@homology_adjunction_family_func B C (@additive_preadditive C Prod t A) t (@additive_terminal_object C Prod t
  A) T0 P Q U D h) v (@homology_adjunction_family_projection_transf B C (@additive_preadditive C Prod t A) t
  (@additive_terminal_object C Prod t A) T0 P Q U D h) (@one_cat_quotient_cokernel_zero B C
  (@additive_preadditive C Prod t A) C1 t (@additive_terminal_object C Prod t A) T0 Q
  (@kernel_adjunction_family_boundary_diagram_func B C (@additive_preadditive C Prod t A) t
  (@additive_terminal_object C Prod t A) P U D h));

// The same derived representative projection cancels whole maps.
symbol one_cat_homology_representative_reflect_path [B C : Cat] (C1 : τ (IsNCat (cat_succ cat_zero) C))
  [Prod : τ (Functor (Product_cat C C) C)] [t : τ (Obj C)] (A : τ (@AdditiveCategory C Prod t)) (T0 : τ
  (@TerminalObject (Op_cat C) t)) (P : τ (@KernelAdjunctionStructure C (@additive_preadditive C Prod t A) t
  (@additive_terminal_object C Prod t A))) (Q : τ (@CokernelAdjunctionStructure C (@additive_preadditive C Prod t
  A) t T0)) (N : τ (@OneCatAdjunctionNormality C (@additive_preadditive C Prod t A) C1 t
  (@additive_terminal_object C Prod t A) T0 P Q)) (U : τ (Functor B C)) (D : τ (Functor B (Functor_cat
  WalkingArrow_cat C))) (h : τ (@Transf B (Functor_cat WalkingArrow_cat C) (@comp_cat_fapp0 B C (Functor_cat
  WalkingArrow_cat C) (@terminal_arrow_diagram_func C t (@additive_terminal_object C Prod t A)) U) D)) (X : τ
  (Functor B C)) (v : τ (@Transf B C X (@homology_adjunction_family_func B C (@additive_preadditive C Prod t A) t
  (@additive_terminal_object C Prod t A) T0 P Q U D h))) (Y : τ (Functor B C)) (a b : τ (@Transf B C X Y)) (e : τ
  (@= (@Transf B C (@kernel_adjunction_family_func B C (@additive_preadditive C Prod t A) t
  (@additive_terminal_object C Prod t A) P (@transf_arrow_diagram_func B C (@fapp0 (Functor_cat B (Product_cat C
  C)) (Functor_cat B C) (@comp_cat_cov_func B (Product_cat C C) C Prod) (@Struct_sigma (Functor B C) (λ _ : τ
  (Functor B C), Functor B C) X (@kernel_adjunction_family_func B C (@additive_preadditive C Prod t A) t
  (@additive_terminal_object C Prod t A) P D))) (@homology_adjunction_family_func B C (@additive_preadditive C
  Prod t A) t (@additive_terminal_object C Prod t A) T0 P Q U D h) (@one_cat_difference_cospan_transf B C C1 Prod
  t A T0 X (@kernel_adjunction_family_func B C (@additive_preadditive C Prod t A) t (@additive_terminal_object C
  Prod t A) P D) (@homology_adjunction_family_func B C (@additive_preadditive C Prod t A) t
  (@additive_terminal_object C Prod t A) T0 P Q U D h) v (@homology_adjunction_family_projection_transf B C
  (@additive_preadditive C Prod t A) t (@additive_terminal_object C Prod t A) T0 P Q U D h)))) Y) (@comp_fapp0
  (Functor_cat B C) (@kernel_adjunction_family_func B C (@additive_preadditive C Prod t A) t
  (@additive_terminal_object C Prod t A) P (@transf_arrow_diagram_func B C (@fapp0 (Functor_cat B (Product_cat C
  C)) (Functor_cat B C) (@comp_cat_cov_func B (Product_cat C C) C Prod) (@Struct_sigma (Functor B C) (λ _ : τ
  (Functor B C), Functor B C) X (@kernel_adjunction_family_func B C (@additive_preadditive C Prod t A) t
  (@additive_terminal_object C Prod t A) P D))) (@homology_adjunction_family_func B C (@additive_preadditive C
  Prod t A) t (@additive_terminal_object C Prod t A) T0 P Q U D h) (@one_cat_difference_cospan_transf B C C1 Prod
  t A T0 X (@kernel_adjunction_family_func B C (@additive_preadditive C Prod t A) t (@additive_terminal_object C
  Prod t A) P D) (@homology_adjunction_family_func B C (@additive_preadditive C Prod t A) t
  (@additive_terminal_object C Prod t A) T0 P Q U D h) v (@homology_adjunction_family_projection_transf B C
  (@additive_preadditive C Prod t A) t (@additive_terminal_object C Prod t A) T0 P Q U D h)))) X Y a
  (@one_cat_homology_representative_projection B C C1 Prod t A T0 P Q N U D h X v)) (@comp_fapp0
  (Functor_cat B C) (@kernel_adjunction_family_func B C (@additive_preadditive C Prod t A) t
  (@additive_terminal_object C Prod t A) P (@transf_arrow_diagram_func B C (@fapp0 (Functor_cat B (Product_cat C
  C)) (Functor_cat B C) (@comp_cat_cov_func B (Product_cat C C) C Prod) (@Struct_sigma (Functor B C) (λ _ : τ
  (Functor B C), Functor B C) X (@kernel_adjunction_family_func B C (@additive_preadditive C Prod t A) t
  (@additive_terminal_object C Prod t A) P D))) (@homology_adjunction_family_func B C (@additive_preadditive C
  Prod t A) t (@additive_terminal_object C Prod t A) T0 P Q U D h) (@one_cat_difference_cospan_transf B C C1 Prod
  t A T0 X (@kernel_adjunction_family_func B C (@additive_preadditive C Prod t A) t (@additive_terminal_object C
  Prod t A) P D) (@homology_adjunction_family_func B C (@additive_preadditive C Prod t A) t
  (@additive_terminal_object C Prod t A) T0 P Q U D h) v (@homology_adjunction_family_projection_transf B C
  (@additive_preadditive C Prod t A) t (@additive_terminal_object C Prod t A) T0 P Q U D h)))) X Y b
  (@one_cat_homology_representative_projection B C C1 Prod t A T0 P Q N U D h X v))))
 : τ (@= (@Transf B C X Y) a b)
≔ @one_cat_cospan_kernel_first_reflect_path B C C1 Prod t A T0 P Q N X (@kernel_adjunction_family_func B C
  (@additive_preadditive C Prod t A) t (@additive_terminal_object C Prod t A) P D)
  (@homology_adjunction_family_func B C (@additive_preadditive C Prod t A) t (@additive_terminal_object C Prod t
  A) T0 P Q U D h) v (@homology_adjunction_family_projection_transf B C (@additive_preadditive C Prod t A) t
  (@additive_terminal_object C Prod t A) T0 P Q U D h) (@one_cat_quotient_cokernel_zero B C
  (@additive_preadditive C Prod t A) C1 t (@additive_terminal_object C Prod t A) T0 Q
  (@kernel_adjunction_family_boundary_diagram_func B C (@additive_preadditive C Prod t A) t
  (@additive_terminal_object C Prod t A) P U D h)) Y a b e;
