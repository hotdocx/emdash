require open emdash.emdash3_2_one_cat_kernel_precomposition_covers;
require open emdash.emdash3_2_one_cat_homology_cover_maps;

// The two original cancellations force the actual cokernel projection of ρ to zero.
symbol one_cat_homology_cover_cokernel_zero [B C : Cat] (C1 : τ (IsNCat (cat_succ cat_zero) C)) [Prod : τ
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
  p))))) (U : τ (Functor B C)) (h : τ (@Transf B (Functor_cat WalkingArrow_cat C) (@comp_cat_fapp0 B C
  (Functor_cat WalkingArrow_cat C) (@terminal_arrow_diagram_func C t (@additive_terminal_object C Prod t A)) U)
  D))
 : τ (@= (@Transf B C (@homology_adjunction_family_func B C (@additive_preadditive C Prod t A) t
  (@additive_terminal_object C Prod t A) T0 P Q U D h) (@cokernel_adjunction_family_func B C
  (@additive_preadditive C Prod t A) t T0 Q (@transf_arrow_diagram_func B C (@kernel_precomposition_family_func B
  C (@additive_preadditive C Prod t A) t (@additive_terminal_object C Prod t A) P M D p)
  (@homology_adjunction_family_func B C (@additive_preadditive C Prod t A) t (@additive_terminal_object C Prod t
  A) T0 P Q U D h) (@one_cat_homology_cover_transf B C (@additive_preadditive C Prod t A) C1 t
  (@additive_terminal_object C Prod t A) T0 P Q U D h M p)))) (@cokernel_adjunction_family_projection_transf B C
  (@additive_preadditive C Prod t A) t T0 Q (@transf_arrow_diagram_func B C (@kernel_precomposition_family_func B
  C (@additive_preadditive C Prod t A) t (@additive_terminal_object C Prod t A) P M D p)
  (@homology_adjunction_family_func B C (@additive_preadditive C Prod t A) t (@additive_terminal_object C Prod t
  A) T0 P Q U D h) (@one_cat_homology_cover_transf B C (@additive_preadditive C Prod t A) C1 t
  (@additive_terminal_object C Prod t A) T0 P Q U D h M p))) (@zero_arrow_family_zero_transf B C t
  (@additive_terminal_object C Prod t A) T0 (@homology_adjunction_family_func B C (@additive_preadditive C Prod t
  A) t (@additive_terminal_object C Prod t A) T0 P Q U D h) (@cokernel_adjunction_family_func B C
  (@additive_preadditive C Prod t A) t T0 Q (@transf_arrow_diagram_func B C (@kernel_precomposition_family_func B
  C (@additive_preadditive C Prod t A) t (@additive_terminal_object C Prod t A) P M D p)
  (@homology_adjunction_family_func B C (@additive_preadditive C Prod t A) t (@additive_terminal_object C Prod t
  A) T0 P Q U D h) (@one_cat_homology_cover_transf B C (@additive_preadditive C Prod t A) C1 t
  (@additive_terminal_object C Prod t A) T0 P Q U D h M p)))))
≔ @one_cat_homology_projection_reflect_path B C (@additive_preadditive C Prod t A) C1 t (@additive_terminal_object
  C Prod t A) T0 P Q U D h (@cokernel_adjunction_family_func B C (@additive_preadditive C Prod t A) t T0 Q
  (@transf_arrow_diagram_func B C (@kernel_precomposition_family_func B C (@additive_preadditive C Prod t A) t
  (@additive_terminal_object C Prod t A) P M D p) (@homology_adjunction_family_func B C (@additive_preadditive C
  Prod t A) t (@additive_terminal_object C Prod t A) T0 P Q U D h) (@one_cat_homology_cover_transf B C
  (@additive_preadditive C Prod t A) C1 t (@additive_terminal_object C Prod t A) T0 P Q U D h M p)))
  (@cokernel_adjunction_family_projection_transf B C (@additive_preadditive C Prod t A) t T0 Q
  (@transf_arrow_diagram_func B C (@kernel_precomposition_family_func B C (@additive_preadditive C Prod t A) t
  (@additive_terminal_object C Prod t A) P M D p) (@homology_adjunction_family_func B C (@additive_preadditive C
  Prod t A) t (@additive_terminal_object C Prod t A) T0 P Q U D h) (@one_cat_homology_cover_transf B C
  (@additive_preadditive C Prod t A) C1 t (@additive_terminal_object C Prod t A) T0 P Q U D h M p)))
  (@zero_arrow_family_zero_transf B C t (@additive_terminal_object C Prod t A) T0
  (@homology_adjunction_family_func B C (@additive_preadditive C Prod t A) t (@additive_terminal_object C Prod t
  A) T0 P Q U D h) (@cokernel_adjunction_family_func B C (@additive_preadditive C Prod t A) t T0 Q
  (@transf_arrow_diagram_func B C (@kernel_precomposition_family_func B C (@additive_preadditive C Prod t A) t
  (@additive_terminal_object C Prod t A) P M D p) (@homology_adjunction_family_func B C (@additive_preadditive C
  Prod t A) t (@additive_terminal_object C Prod t A) T0 P Q U D h) (@one_cat_homology_cover_transf B C
  (@additive_preadditive C Prod t A) C1 t (@additive_terminal_object C Prod t A) T0 P Q U D h M p)))) (@eq_trans _
  _ _ _ (@one_cat_kernel_precomposition_reflect_path B C C1 Prod t A T0 P Q N M D p zp
  (@cokernel_adjunction_family_func B C (@additive_preadditive C Prod t A) t T0 Q (@transf_arrow_diagram_func B C
  (@kernel_precomposition_family_func B C (@additive_preadditive C Prod t A) t (@additive_terminal_object C Prod t
  A) P M D p) (@homology_adjunction_family_func B C (@additive_preadditive C Prod t A) t
  (@additive_terminal_object C Prod t A) T0 P Q U D h) (@one_cat_homology_cover_transf B C (@additive_preadditive
  C Prod t A) C1 t (@additive_terminal_object C Prod t A) T0 P Q U D h M p))) (@comp_fapp0 (Functor_cat B C)
  (@kernel_adjunction_family_func B C (@additive_preadditive C Prod t A) t (@additive_terminal_object C Prod t A)
  P D) (@homology_adjunction_family_func B C (@additive_preadditive C Prod t A) t (@additive_terminal_object C
  Prod t A) T0 P Q U D h) (@cokernel_adjunction_family_func B C (@additive_preadditive C Prod t A) t T0 Q
  (@transf_arrow_diagram_func B C (@kernel_precomposition_family_func B C (@additive_preadditive C Prod t A) t
  (@additive_terminal_object C Prod t A) P M D p) (@homology_adjunction_family_func B C (@additive_preadditive C
  Prod t A) t (@additive_terminal_object C Prod t A) T0 P Q U D h) (@one_cat_homology_cover_transf B C
  (@additive_preadditive C Prod t A) C1 t (@additive_terminal_object C Prod t A) T0 P Q U D h M p)))
  (@cokernel_adjunction_family_projection_transf B C (@additive_preadditive C Prod t A) t T0 Q
  (@transf_arrow_diagram_func B C (@kernel_precomposition_family_func B C (@additive_preadditive C Prod t A) t
  (@additive_terminal_object C Prod t A) P M D p) (@homology_adjunction_family_func B C (@additive_preadditive C
  Prod t A) t (@additive_terminal_object C Prod t A) T0 P Q U D h) (@one_cat_homology_cover_transf B C
  (@additive_preadditive C Prod t A) C1 t (@additive_terminal_object C Prod t A) T0 P Q U D h M p)))
  (@homology_adjunction_family_projection_transf B C (@additive_preadditive C Prod t A) t
  (@additive_terminal_object C Prod t A) T0 P Q U D h)) (@zero_arrow_family_zero_transf B C t
  (@additive_terminal_object C Prod t A) T0 (@kernel_adjunction_family_func B C (@additive_preadditive C Prod t A)
  t (@additive_terminal_object C Prod t A) P D) (@cokernel_adjunction_family_func B C (@additive_preadditive C
  Prod t A) t T0 Q (@transf_arrow_diagram_func B C (@kernel_precomposition_family_func B C (@additive_preadditive
  C Prod t A) t (@additive_terminal_object C Prod t A) P M D p) (@homology_adjunction_family_func B C
  (@additive_preadditive C Prod t A) t (@additive_terminal_object C Prod t A) T0 P Q U D h)
  (@one_cat_homology_cover_transf B C (@additive_preadditive C Prod t A) C1 t (@additive_terminal_object C Prod t
  A) T0 P Q U D h M p)))) (@eq_trans _ _ _ _ (@eq_sym _ _ _ (@comp_assoc (Functor_cat B C)
  (@kernel_precomposition_family_func B C (@additive_preadditive C Prod t A) t (@additive_terminal_object C Prod t
  A) P M D p) (@kernel_adjunction_family_func B C (@additive_preadditive C Prod t A) t (@additive_terminal_object
  C Prod t A) P D) (@homology_adjunction_family_func B C (@additive_preadditive C Prod t A) t
  (@additive_terminal_object C Prod t A) T0 P Q U D h) (@cokernel_adjunction_family_func B C
  (@additive_preadditive C Prod t A) t T0 Q (@transf_arrow_diagram_func B C (@kernel_precomposition_family_func B
  C (@additive_preadditive C Prod t A) t (@additive_terminal_object C Prod t A) P M D p)
  (@homology_adjunction_family_func B C (@additive_preadditive C Prod t A) t (@additive_terminal_object C Prod t
  A) T0 P Q U D h) (@one_cat_homology_cover_transf B C (@additive_preadditive C Prod t A) C1 t
  (@additive_terminal_object C Prod t A) T0 P Q U D h M p))) (@cokernel_adjunction_family_projection_transf B C
  (@additive_preadditive C Prod t A) t T0 Q (@transf_arrow_diagram_func B C (@kernel_precomposition_family_func B
  C (@additive_preadditive C Prod t A) t (@additive_terminal_object C Prod t A) P M D p)
  (@homology_adjunction_family_func B C (@additive_preadditive C Prod t A) t (@additive_terminal_object C Prod t
  A) T0 P Q U D h) (@one_cat_homology_cover_transf B C (@additive_preadditive C Prod t A) C1 t
  (@additive_terminal_object C Prod t A) T0 P Q U D h M p))) (@homology_adjunction_family_projection_transf B C
  (@additive_preadditive C Prod t A) t (@additive_terminal_object C Prod t A) T0 P Q U D h)
  (@one_cat_kernel_precomposition_second_transf B C (@additive_preadditive C Prod t A) C1 t
  (@additive_terminal_object C Prod t A) T0 P M D p))) (@eq_trans _ _ _ _
  (@one_cat_cokernel_family_annihilation_path B C (@additive_preadditive C Prod t A) C1 t
  (@additive_terminal_object C Prod t A) T0 Q (@transf_arrow_diagram_func B C (@kernel_precomposition_family_func
  B C (@additive_preadditive C Prod t A) t (@additive_terminal_object C Prod t A) P M D p)
  (@homology_adjunction_family_func B C (@additive_preadditive C Prod t A) t (@additive_terminal_object C Prod t
  A) T0 P Q U D h) (@one_cat_homology_cover_transf B C (@additive_preadditive C Prod t A) C1 t
  (@additive_terminal_object C Prod t A) T0 P Q U D h M p))) (@eq_sym _ _ _ (@one_cat_zero_family_precompose_path
  B C C1 t (@additive_terminal_object C Prod t A) T0 (@kernel_precomposition_family_func B C
  (@additive_preadditive C Prod t A) t (@additive_terminal_object C Prod t A) P M D p)
  (@kernel_adjunction_family_func B C (@additive_preadditive C Prod t A) t (@additive_terminal_object C Prod t A)
  P D) (@cokernel_adjunction_family_func B C (@additive_preadditive C Prod t A) t T0 Q (@transf_arrow_diagram_func
  B C (@kernel_precomposition_family_func B C (@additive_preadditive C Prod t A) t (@additive_terminal_object C
  Prod t A) P M D p) (@homology_adjunction_family_func B C (@additive_preadditive C Prod t A) t
  (@additive_terminal_object C Prod t A) T0 P Q U D h) (@one_cat_homology_cover_transf B C (@additive_preadditive
  C Prod t A) C1 t (@additive_terminal_object C Prod t A) T0 P Q U D h M p)))
  (@one_cat_kernel_precomposition_second_transf B C (@additive_preadditive C Prod t A) C1 t
  (@additive_terminal_object C Prod t A) T0 P M D p)))))) (@eq_sym _ _ _ (@one_cat_zero_family_precompose_path B C
  C1 t (@additive_terminal_object C Prod t A) T0 (@kernel_adjunction_family_func B C (@additive_preadditive C Prod
  t A) t (@additive_terminal_object C Prod t A) P D) (@homology_adjunction_family_func B C (@additive_preadditive
  C Prod t A) t (@additive_terminal_object C Prod t A) T0 P Q U D h) (@cokernel_adjunction_family_func B C
  (@additive_preadditive C Prod t A) t T0 Q (@transf_arrow_diagram_func B C (@kernel_precomposition_family_func B
  C (@additive_preadditive C Prod t A) t (@additive_terminal_object C Prod t A) P M D p)
  (@homology_adjunction_family_func B C (@additive_preadditive C Prod t A) t (@additive_terminal_object C Prod t
  A) T0 P Q U D h) (@one_cat_homology_cover_transf B C (@additive_preadditive C Prod t A) C1 t
  (@additive_terminal_object C Prod t A) T0 P Q U D h M p))) (@homology_adjunction_family_projection_transf B C
  (@additive_preadditive C Prod t A) t (@additive_terminal_object C Prod t A) T0 P Q U D h))));

// This is fixed-forward cover evidence for the original ρ and original H.
symbol one_cat_homology_cover_omega [B C : Cat] (C1 : τ (IsNCat (cat_succ cat_zero) C)) [Prod : τ (Functor
  (Product_cat C C) C)] [t : τ (Obj C)] (A : τ (@AdditiveCategory C Prod t)) (T0 : τ (@TerminalObject (Op_cat C)
  t)) (P : τ (@KernelAdjunctionStructure C (@additive_preadditive C Prod t A) t (@additive_terminal_object C Prod
  t A))) (Q : τ (@CokernelAdjunctionStructure C (@additive_preadditive C Prod t A) t T0)) (N : τ
  (@OneCatAdjunctionNormality C (@additive_preadditive C Prod t A) C1 t (@additive_terminal_object C Prod t A) T0
  P Q)) (M : τ (Functor B C)) (D : τ (Functor B (Functor_cat WalkingArrow_cat C))) (p : τ (@Transf B C M
  (@diagram_family_at_func B WalkingArrow_cat C D walking_arrow_src))) (zp : τ (@= (@Transf B C
  (@diagram_family_at_func B WalkingArrow_cat C D walking_arrow_src) (@cokernel_adjunction_family_func B C
  (@additive_preadditive C Prod t A) t T0 Q (@transf_arrow_diagram_func B C M (@diagram_family_at_func B
  WalkingArrow_cat C D walking_arrow_src) p))) (@cokernel_adjunction_family_projection_transf B C
  (@additive_preadditive C Prod t A) t T0 Q (@transf_arrow_diagram_func B C M (@diagram_family_at_func B
  WalkingArrow_cat C D walking_arrow_src) p)) (@zero_arrow_family_zero_transf B C t (@additive_terminal_object C
  Prod t A) T0 (@diagram_family_at_func B WalkingArrow_cat C D walking_arrow_src)
  (@cokernel_adjunction_family_func B C (@additive_preadditive C Prod t A) t T0 Q (@transf_arrow_diagram_func B C
  M (@diagram_family_at_func B WalkingArrow_cat C D walking_arrow_src) p))))) (U : τ (Functor B C)) (h : τ
  (@Transf B (Functor_cat WalkingArrow_cat C) (@comp_cat_fapp0 B C (Functor_cat WalkingArrow_cat C)
  (@terminal_arrow_diagram_func C t (@additive_terminal_object C Prod t A)) U) D))
 : τ (@OmegaEquivAlong (Functor_cat B C) (@comp_cat_fapp0 B (Functor_cat WalkingArrow_cat C) C
  (@adjunction_coimage_func C (@additive_preadditive C Prod t A) t (@additive_terminal_object C Prod t A) T0 P Q)
  (@transf_arrow_diagram_func B C (@kernel_precomposition_family_func B C (@additive_preadditive C Prod t A) t
  (@additive_terminal_object C Prod t A) P M D p) (@homology_adjunction_family_func B C (@additive_preadditive C
  Prod t A) t (@additive_terminal_object C Prod t A) T0 P Q U D h) (@one_cat_homology_cover_transf B C
  (@additive_preadditive C Prod t A) C1 t (@additive_terminal_object C Prod t A) T0 P Q U D h M p)))
  (@homology_adjunction_family_func B C (@additive_preadditive C Prod t A) t (@additive_terminal_object C Prod t
  A) T0 P Q U D h) (@fapp0 _ _ (@comp_cat_con_fapp1_func B (Functor_cat WalkingArrow_cat C) C
  (@transf_arrow_diagram_func B C (@kernel_precomposition_family_func B C (@additive_preadditive C Prod t A) t
  (@additive_terminal_object C Prod t A) P M D p) (@homology_adjunction_family_func B C (@additive_preadditive C
  Prod t A) t (@additive_terminal_object C Prod t A) T0 P Q U D h) (@one_cat_homology_cover_transf B C
  (@additive_preadditive C Prod t A) C1 t (@additive_terminal_object C Prod t A) T0 P Q U D h M p))
  (@adjunction_coimage_func C (@additive_preadditive C Prod t A) t (@additive_terminal_object C Prod t A) T0 P Q)
  (@diagram_evaluation_at_func WalkingArrow_cat C walking_arrow_tgt)) (@one_cat_adjunction_coimage_to_target C
  (@additive_preadditive C Prod t A) C1 t (@additive_terminal_object C Prod t A) T0 P Q)))
≔ @one_cat_zero_cokernel_cover_omega B C (@additive_preadditive C Prod t A) C1 t (@additive_terminal_object C Prod
  t A) T0 P Q N (@transf_arrow_diagram_func B C (@kernel_precomposition_family_func B C (@additive_preadditive C
  Prod t A) t (@additive_terminal_object C Prod t A) P M D p) (@homology_adjunction_family_func B C
  (@additive_preadditive C Prod t A) t (@additive_terminal_object C Prod t A) T0 P Q U D h)
  (@one_cat_homology_cover_transf B C (@additive_preadditive C Prod t A) C1 t (@additive_terminal_object C Prod t
  A) T0 P Q U D h M p)) (@one_cat_homology_cover_cokernel_zero B C C1 Prod t A T0 P Q N M D p zp U h);
