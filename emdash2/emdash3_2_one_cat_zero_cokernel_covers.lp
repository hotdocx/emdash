require open emdash.emdash3_2_one_cat_zero_kernel_families;
require open emdash.emdash3_2_omega_equiv_composition;
require open emdash.emdash3_2_one_cat_coimage_factor_paths;
require open emdash.emdash3_2_one_cat_adjunction_normality;
require open emdash.emdash3_2_reindex_composition_paths;

// The image inclusion retains the original kernel of the original restricted quotient.
symbol one_cat_image_family_kernel_path [B C : Cat] [S : τ (@PreadditiveCategory C)] (C1 : τ (IsNCat
  (cat_succ cat_zero) C)) [t : τ (Obj C)] (T : τ (@TerminalObject C t)) (T0 : τ (@TerminalObject (Op_cat C) t)) (P
  : τ (@KernelAdjunctionStructure C S t T)) (Q : τ (@CokernelAdjunctionStructure C S t T0)) (D : τ (Functor B
  (Functor_cat WalkingArrow_cat C)))
 : τ (@= (@Transf B C (@comp_cat_fapp0 B (Functor_cat WalkingArrow_cat C) C (@adjunction_image_func C S t T T0 P
  Q) D) (@diagram_family_at_func B WalkingArrow_cat C D walking_arrow_tgt))
  (@kernel_adjunction_family_inclusion_transf B C S t T P (@comp_cat_fapp0 B (Functor_cat WalkingArrow_cat C)
  (Functor_cat WalkingArrow_cat C) (@cokernel_adjunction_arrow_func C S t T0 Q) D)) (@fapp0 _ _
  (@comp_cat_con_fapp1_func B (Functor_cat WalkingArrow_cat C) C D (@adjunction_image_func C S t T T0 P Q)
  (@diagram_evaluation_at_func WalkingArrow_cat C walking_arrow_tgt)) (@adjunction_image_inclusion C S t T T0 P
  Q)))
≔ @eq_trans _ _ _ _ (@one_cat_kernel_family_inclusion_whisker_path B C S C1 t T P (@comp_cat_fapp0 B (Functor_cat
  WalkingArrow_cat C) (Functor_cat WalkingArrow_cat C) (@cokernel_adjunction_arrow_func C S t T0 Q) D)) (@eq_sym _
  _ _ (@prewhisker_assoc_path B (Functor_cat WalkingArrow_cat C) (Functor_cat WalkingArrow_cat C) C D
  (@cokernel_adjunction_arrow_func C S t T0 Q) (@kernel_adjunction_func C S t T P) (@diagram_evaluation_at_func
  WalkingArrow_cat C walking_arrow_src) (@kernel_adjunction_inclusion C S t T P)));

// Whole endpoint uniqueness retains the actual quotient while presenting its image diagram.
symbol one_cat_cokernel_zero_image_diagram_path [B C : Cat] [S : τ (@PreadditiveCategory C)] (C1 : τ (IsNCat
  (cat_succ cat_zero) C)) [t : τ (Obj C)] (T : τ (@TerminalObject C t)) (T0 : τ (@TerminalObject (Op_cat C) t)) (P
  : τ (@KernelAdjunctionStructure C S t T)) (Q : τ (@CokernelAdjunctionStructure C S t T0)) (D : τ (Functor B
  (Functor_cat WalkingArrow_cat C))) (z : τ (@= (@Transf B C (@diagram_family_at_func B WalkingArrow_cat C D
  walking_arrow_tgt) (@comp_cat_fapp0 B (Functor_cat WalkingArrow_cat C) C (@cokernel_adjunction_func C S t T0 Q)
  D)) (@cokernel_adjunction_family_projection_transf B C S t T0 Q D) (@zero_arrow_family_zero_transf B C t T T0
  (@diagram_family_at_func B WalkingArrow_cat C D walking_arrow_tgt) (@comp_cat_fapp0 B (Functor_cat
  WalkingArrow_cat C) C (@cokernel_adjunction_func C S t T0 Q) D))))
 : τ (@= (@Transf B C (@diagram_family_at_func B WalkingArrow_cat C (@comp_cat_fapp0 B (Functor_cat
  WalkingArrow_cat C) (Functor_cat WalkingArrow_cat C) (@cokernel_adjunction_arrow_func C S t T0 Q) D)
  walking_arrow_src) (@diagram_family_at_func B WalkingArrow_cat C (@comp_cat_fapp0 B (Functor_cat
  WalkingArrow_cat C) (Functor_cat WalkingArrow_cat C) (@cokernel_adjunction_arrow_func C S t T0 Q) D)
  walking_arrow_tgt)) (@diagram_family_transf B WalkingArrow_cat C (@comp_cat_fapp0 B (Functor_cat
  WalkingArrow_cat C) (Functor_cat WalkingArrow_cat C) (@cokernel_adjunction_arrow_func C S t T0 Q) D)
  walking_arrow_src walking_arrow_tgt walking_arrow_generator) (@zero_arrow_family_zero_transf B C t T T0
  (@diagram_family_at_func B WalkingArrow_cat C (@comp_cat_fapp0 B (Functor_cat WalkingArrow_cat C) (Functor_cat
  WalkingArrow_cat C) (@cokernel_adjunction_arrow_func C S t T0 Q) D) walking_arrow_src) (@diagram_family_at_func
  B WalkingArrow_cat C (@comp_cat_fapp0 B (Functor_cat WalkingArrow_cat C) (Functor_cat WalkingArrow_cat C)
  (@cokernel_adjunction_arrow_func C S t T0 Q) D) walking_arrow_tgt)))
≔ @eq_trans _ _ _ _ z (@eq_trans _ _ _ _ (@eq_ap (@Transf B C (@diagram_family_at_func B WalkingArrow_cat C
  (@comp_cat_fapp0 B (Functor_cat WalkingArrow_cat C) (Functor_cat WalkingArrow_cat C)
  (@cokernel_adjunction_arrow_func C S t T0 Q) D) walking_arrow_src) (@Const_func B C t)) (@Transf B C
  (@diagram_family_at_func B WalkingArrow_cat C (@comp_cat_fapp0 B (Functor_cat WalkingArrow_cat C) (Functor_cat
  WalkingArrow_cat C) (@cokernel_adjunction_arrow_func C S t T0 Q) D) walking_arrow_src) (@comp_cat_fapp0 B
  (Functor_cat WalkingArrow_cat C) C (@cokernel_adjunction_func C S t T0 Q) D)) (λ v : τ (@Transf B C
  (@diagram_family_at_func B WalkingArrow_cat C (@comp_cat_fapp0 B (Functor_cat WalkingArrow_cat C) (Functor_cat
  WalkingArrow_cat C) (@cokernel_adjunction_arrow_func C S t T0 Q) D) walking_arrow_src) (@Const_func B C t)),
  (@comp_fapp0 (Functor_cat B C) (@diagram_family_at_func B WalkingArrow_cat C (@comp_cat_fapp0 B (Functor_cat
  WalkingArrow_cat C) (Functor_cat WalkingArrow_cat C) (@cokernel_adjunction_arrow_func C S t T0 Q) D)
  walking_arrow_src) (@Const_func B C t) (@comp_cat_fapp0 B (Functor_cat WalkingArrow_cat C) C
  (@cokernel_adjunction_func C S t T0 Q) D) (@diagram_family_transf B WalkingArrow_cat C (@comp_cat_fapp0 B C
  (Functor_cat WalkingArrow_cat C) (@initial_arrow_diagram_func C t T0) (@comp_cat_fapp0 B (Functor_cat
  WalkingArrow_cat C) C (@cokernel_adjunction_func C S t T0 Q) D)) walking_arrow_src walking_arrow_tgt
  walking_arrow_generator) v)) (@diagram_family_transf B WalkingArrow_cat C (@comp_cat_fapp0 B C (Functor_cat
  WalkingArrow_cat C) (@terminal_arrow_diagram_func C t T) (@diagram_family_at_func B WalkingArrow_cat C D
  walking_arrow_tgt)) walking_arrow_src walking_arrow_tgt walking_arrow_generator) (@diagram_family_transf B
  WalkingArrow_cat C (@comp_cat_fapp0 B C (Functor_cat WalkingArrow_cat C) (@terminal_arrow_diagram_func C t T)
  (@diagram_family_at_func B WalkingArrow_cat C (@comp_cat_fapp0 B (Functor_cat WalkingArrow_cat C) (Functor_cat
  WalkingArrow_cat C) (@cokernel_adjunction_arrow_func C S t T0 Q) D) walking_arrow_src)) walking_arrow_src
  walking_arrow_tgt walking_arrow_generator) (@one_cat_terminal_family_arrow_path B C C1 t T
  (@diagram_family_at_func B WalkingArrow_cat C (@comp_cat_fapp0 B (Functor_cat WalkingArrow_cat C) (Functor_cat
  WalkingArrow_cat C) (@cokernel_adjunction_arrow_func C S t T0 Q) D) walking_arrow_src) (@diagram_family_transf B
  WalkingArrow_cat C (@comp_cat_fapp0 B C (Functor_cat WalkingArrow_cat C) (@terminal_arrow_diagram_func C t T)
  (@diagram_family_at_func B WalkingArrow_cat C D walking_arrow_tgt)) walking_arrow_src walking_arrow_tgt
  walking_arrow_generator))) (@eq_ap (@Transf B C (@Const_func B C t) (@diagram_family_at_func B WalkingArrow_cat
  C (@comp_cat_fapp0 B (Functor_cat WalkingArrow_cat C) (Functor_cat WalkingArrow_cat C)
  (@cokernel_adjunction_arrow_func C S t T0 Q) D) walking_arrow_tgt)) (@Transf B C (@diagram_family_at_func B
  WalkingArrow_cat C (@comp_cat_fapp0 B (Functor_cat WalkingArrow_cat C) (Functor_cat WalkingArrow_cat C)
  (@cokernel_adjunction_arrow_func C S t T0 Q) D) walking_arrow_src) (@diagram_family_at_func B WalkingArrow_cat C
  (@comp_cat_fapp0 B (Functor_cat WalkingArrow_cat C) (Functor_cat WalkingArrow_cat C)
  (@cokernel_adjunction_arrow_func C S t T0 Q) D) walking_arrow_tgt)) (λ v : τ (@Transf B C (@Const_func B C t)
  (@diagram_family_at_func B WalkingArrow_cat C (@comp_cat_fapp0 B (Functor_cat WalkingArrow_cat C) (Functor_cat
  WalkingArrow_cat C) (@cokernel_adjunction_arrow_func C S t T0 Q) D) walking_arrow_tgt)), (@comp_fapp0
  (Functor_cat B C) (@diagram_family_at_func B WalkingArrow_cat C (@comp_cat_fapp0 B (Functor_cat WalkingArrow_cat
  C) (Functor_cat WalkingArrow_cat C) (@cokernel_adjunction_arrow_func C S t T0 Q) D) walking_arrow_src)
  (@Const_func B C t) (@diagram_family_at_func B WalkingArrow_cat C (@comp_cat_fapp0 B (Functor_cat
  WalkingArrow_cat C) (Functor_cat WalkingArrow_cat C) (@cokernel_adjunction_arrow_func C S t T0 Q) D)
  walking_arrow_tgt) v (@diagram_family_transf B WalkingArrow_cat C (@comp_cat_fapp0 B C (Functor_cat
  WalkingArrow_cat C) (@terminal_arrow_diagram_func C t T) (@diagram_family_at_func B WalkingArrow_cat C
  (@comp_cat_fapp0 B (Functor_cat WalkingArrow_cat C) (Functor_cat WalkingArrow_cat C)
  (@cokernel_adjunction_arrow_func C S t T0 Q) D) walking_arrow_src)) walking_arrow_src walking_arrow_tgt
  walking_arrow_generator))) (@diagram_family_transf B WalkingArrow_cat C (@comp_cat_fapp0 B C (Functor_cat
  WalkingArrow_cat C) (@initial_arrow_diagram_func C t T0) (@comp_cat_fapp0 B (Functor_cat WalkingArrow_cat C) C
  (@cokernel_adjunction_func C S t T0 Q) D)) walking_arrow_src walking_arrow_tgt walking_arrow_generator)
  (@diagram_family_transf B WalkingArrow_cat C (@comp_cat_fapp0 B C (Functor_cat WalkingArrow_cat C)
  (@initial_arrow_diagram_func C t T0) (@diagram_family_at_func B WalkingArrow_cat C (@comp_cat_fapp0 B
  (Functor_cat WalkingArrow_cat C) (Functor_cat WalkingArrow_cat C) (@cokernel_adjunction_arrow_func C S t T0 Q)
  D) walking_arrow_tgt)) walking_arrow_src walking_arrow_tgt walking_arrow_generator)
  (@one_cat_initial_family_arrow_path B C C1 t T0 (@diagram_family_at_func B WalkingArrow_cat C (@comp_cat_fapp0 B
  (Functor_cat WalkingArrow_cat C) (Functor_cat WalkingArrow_cat C) (@cokernel_adjunction_arrow_func C S t T0 Q)
  D) walking_arrow_tgt) (@diagram_family_transf B WalkingArrow_cat C (@comp_cat_fapp0 B C (Functor_cat
  WalkingArrow_cat C) (@initial_arrow_diagram_func C t T0) (@comp_cat_fapp0 B (Functor_cat WalkingArrow_cat C) C
  (@cokernel_adjunction_func C S t T0 Q) D)) walking_arrow_src walking_arrow_tgt walking_arrow_generator))));

// When the actual cokernel projection is zero, its original image inclusion is invertible.
symbol one_cat_zero_cokernel_image_omega [B C : Cat] [S : τ (@PreadditiveCategory C)] (C1 : τ (IsNCat
  (cat_succ cat_zero) C)) [t : τ (Obj C)] (T : τ (@TerminalObject C t)) (T0 : τ (@TerminalObject (Op_cat C) t)) (P
  : τ (@KernelAdjunctionStructure C S t T)) (Q : τ (@CokernelAdjunctionStructure C S t T0)) (D : τ (Functor B
  (Functor_cat WalkingArrow_cat C))) (z : τ (@= (@Transf B C (@diagram_family_at_func B WalkingArrow_cat C D
  walking_arrow_tgt) (@comp_cat_fapp0 B (Functor_cat WalkingArrow_cat C) C (@cokernel_adjunction_func C S t T0 Q)
  D)) (@cokernel_adjunction_family_projection_transf B C S t T0 Q D) (@zero_arrow_family_zero_transf B C t T T0
  (@diagram_family_at_func B WalkingArrow_cat C D walking_arrow_tgt) (@comp_cat_fapp0 B (Functor_cat
  WalkingArrow_cat C) C (@cokernel_adjunction_func C S t T0 Q) D))))
 : τ (@OmegaEquivAlong (Functor_cat B C) (@comp_cat_fapp0 B (Functor_cat WalkingArrow_cat C) C
  (@adjunction_image_func C S t T T0 P Q) D) (@diagram_family_at_func B WalkingArrow_cat C D walking_arrow_tgt)
  (@fapp0 _ _ (@comp_cat_con_fapp1_func B (Functor_cat WalkingArrow_cat C) C D (@adjunction_image_func C S t T T0
  P Q) (@diagram_evaluation_at_func WalkingArrow_cat C walking_arrow_tgt)) (@adjunction_image_inclusion C S t T T0
  P Q)))
≔ @omega_equiv_along_equal (Functor_cat B C) (@comp_cat_fapp0 B (Functor_cat WalkingArrow_cat C) C
  (@adjunction_image_func C S t T T0 P Q) D) (@diagram_family_at_func B WalkingArrow_cat C D walking_arrow_tgt)
  (@kernel_adjunction_family_inclusion_transf B C S t T P (@comp_cat_fapp0 B (Functor_cat WalkingArrow_cat C)
  (Functor_cat WalkingArrow_cat C) (@cokernel_adjunction_arrow_func C S t T0 Q) D)) (@fapp0 _ _
  (@comp_cat_con_fapp1_func B (Functor_cat WalkingArrow_cat C) C D (@adjunction_image_func C S t T T0 P Q)
  (@diagram_evaluation_at_func WalkingArrow_cat C walking_arrow_tgt)) (@adjunction_image_inclusion C S t T T0 P
  Q)) (@one_cat_zero_kernel_omega B C S C1 t T T0 P (@comp_cat_fapp0 B (Functor_cat WalkingArrow_cat C)
  (Functor_cat WalkingArrow_cat C) (@cokernel_adjunction_arrow_func C S t T0 Q) D)
  (@one_cat_cokernel_zero_image_diagram_path B C S C1 t T T0 P Q D z))
  (@one_cat_image_family_kernel_path B C S C1 t T T0 P Q D);

// Restriction preserves the equality with the original coimage-to-target map.
symbol one_cat_coimage_target_family_factor_path [B C : Cat] [S : τ (@PreadditiveCategory C)] (C1 : τ
  (IsNCat (cat_succ cat_zero) C)) [t : τ (Obj C)] (T : τ (@TerminalObject C t)) (T0 : τ (@TerminalObject (Op_cat
  C) t)) (P : τ (@KernelAdjunctionStructure C S t T)) (Q : τ (@CokernelAdjunctionStructure C S t T0)) (D : τ
  (Functor B (Functor_cat WalkingArrow_cat C)))
 : τ (@= (@Transf B C (@comp_cat_fapp0 B (Functor_cat WalkingArrow_cat C) C (@adjunction_coimage_func C S t T T0 P
  Q) D) (@diagram_family_at_func B WalkingArrow_cat C D walking_arrow_tgt)) (@comp_fapp0 (Functor_cat B C)
  (@comp_cat_fapp0 B (Functor_cat WalkingArrow_cat C) C (@adjunction_coimage_func C S t T T0 P Q) D)
  (@comp_cat_fapp0 B (Functor_cat WalkingArrow_cat C) C (@adjunction_image_func C S t T T0 P Q) D)
  (@diagram_family_at_func B WalkingArrow_cat C D walking_arrow_tgt) (@fapp0 _ _ (@comp_cat_con_fapp1_func B
  (Functor_cat WalkingArrow_cat C) C D (@adjunction_image_func C S t T T0 P Q) (@diagram_evaluation_at_func
  WalkingArrow_cat C walking_arrow_tgt)) (@adjunction_image_inclusion C S t T T0 P Q)) (@fapp0 _ _
  (@comp_cat_con_fapp1_func B (Functor_cat WalkingArrow_cat C) C D (@adjunction_coimage_func C S t T T0 P Q)
  (@adjunction_image_func C S t T T0 P Q)) (@one_cat_coimage_image_comparison C S C1 t T T0 P Q))) (@fapp0 _ _
  (@comp_cat_con_fapp1_func B (Functor_cat WalkingArrow_cat C) C D (@adjunction_coimage_func C S t T T0 P Q)
  (@diagram_evaluation_at_func WalkingArrow_cat C walking_arrow_tgt)) (@one_cat_adjunction_coimage_to_target C S
  C1 t T T0 P Q)))
≔ (@eq_trans _ _ _ _ (@eq_sym _ _ _ (@prewhisker_comp_path B (Functor_cat WalkingArrow_cat C) C D
  (@adjunction_coimage_func C S t T T0 P Q) (@adjunction_image_func C S t T T0 P Q) (@diagram_evaluation_at_func
  WalkingArrow_cat C walking_arrow_tgt) (@one_cat_coimage_image_comparison C S C1 t T T0 P Q)
  (@adjunction_image_inclusion C S t T T0 P Q))) (@eq_ap (@Transf (Functor_cat WalkingArrow_cat C) C
  (@adjunction_coimage_func C S t T T0 P Q) (@diagram_evaluation_at_func WalkingArrow_cat C walking_arrow_tgt))
  (@Transf B C (@comp_cat_fapp0 B (Functor_cat WalkingArrow_cat C) C (@adjunction_coimage_func C S t T T0 P Q) D)
  (@diagram_family_at_func B WalkingArrow_cat C D walking_arrow_tgt)) (λ v : τ (@Transf (Functor_cat
  WalkingArrow_cat C) C (@adjunction_coimage_func C S t T T0 P Q) (@diagram_evaluation_at_func WalkingArrow_cat C
  walking_arrow_tgt)), (@fapp0 _ _ (@comp_cat_con_fapp1_func B (Functor_cat WalkingArrow_cat C) C D
  (@adjunction_coimage_func C S t T T0 P Q) (@diagram_evaluation_at_func WalkingArrow_cat C walking_arrow_tgt))
  v)) (@comp_fapp0 (Functor_cat (Functor_cat WalkingArrow_cat C) C) (@adjunction_coimage_func C S t T T0 P Q)
  (@adjunction_image_func C S t T T0 P Q) (@diagram_evaluation_at_func WalkingArrow_cat C walking_arrow_tgt)
  (@adjunction_image_inclusion C S t T T0 P Q) (@one_cat_coimage_image_comparison C S C1 t T T0 P Q))
  (@one_cat_adjunction_coimage_to_target C S C1 t T T0 P Q) (@one_cat_coimage_target_image_factor_path C S
  C1 t T T0 P Q)));

// Original normality and the zero-cokernel proof make the actual coimage factor invertible.
symbol one_cat_zero_cokernel_cover_omega [B C : Cat] [S : τ (@PreadditiveCategory C)] (C1 : τ (IsNCat
  (cat_succ cat_zero) C)) [t : τ (Obj C)] (T : τ (@TerminalObject C t)) (T0 : τ (@TerminalObject (Op_cat C) t)) (P
  : τ (@KernelAdjunctionStructure C S t T)) (Q : τ (@CokernelAdjunctionStructure C S t T0)) (N : τ
  (@OneCatAdjunctionNormality C S C1 t T T0 P Q)) (D : τ (Functor B (Functor_cat WalkingArrow_cat C))) (z : τ (@=
  (@Transf B C (@diagram_family_at_func B WalkingArrow_cat C D walking_arrow_tgt) (@comp_cat_fapp0 B (Functor_cat
  WalkingArrow_cat C) C (@cokernel_adjunction_func C S t T0 Q) D)) (@cokernel_adjunction_family_projection_transf
  B C S t T0 Q D) (@zero_arrow_family_zero_transf B C t T T0 (@diagram_family_at_func B WalkingArrow_cat C D
  walking_arrow_tgt) (@comp_cat_fapp0 B (Functor_cat WalkingArrow_cat C) C (@cokernel_adjunction_func C S t T0 Q)
  D))))
 : τ (@OmegaEquivAlong (Functor_cat B C) (@comp_cat_fapp0 B (Functor_cat WalkingArrow_cat C) C
  (@adjunction_coimage_func C S t T T0 P Q) D) (@diagram_family_at_func B WalkingArrow_cat C D walking_arrow_tgt)
  (@fapp0 _ _ (@comp_cat_con_fapp1_func B (Functor_cat WalkingArrow_cat C) C D (@adjunction_coimage_func C S t T
  T0 P Q) (@diagram_evaluation_at_func WalkingArrow_cat C walking_arrow_tgt))
  (@one_cat_adjunction_coimage_to_target C S C1 t T T0 P Q)))
≔ @omega_equiv_along_equal (Functor_cat B C) (@comp_cat_fapp0 B (Functor_cat WalkingArrow_cat C) C
  (@adjunction_coimage_func C S t T T0 P Q) D) (@diagram_family_at_func B WalkingArrow_cat C D walking_arrow_tgt)
  (@comp_fapp0 (Functor_cat B C) (@comp_cat_fapp0 B (Functor_cat WalkingArrow_cat C) C (@adjunction_coimage_func C
  S t T T0 P Q) D) (@comp_cat_fapp0 B (Functor_cat WalkingArrow_cat C) C (@adjunction_image_func C S t T T0 P Q)
  D) (@diagram_family_at_func B WalkingArrow_cat C D walking_arrow_tgt) (@fapp0 _ _ (@comp_cat_con_fapp1_func B
  (Functor_cat WalkingArrow_cat C) C D (@adjunction_image_func C S t T T0 P Q) (@diagram_evaluation_at_func
  WalkingArrow_cat C walking_arrow_tgt)) (@adjunction_image_inclusion C S t T T0 P Q)) (@fapp0 _ _
  (@comp_cat_con_fapp1_func B (Functor_cat WalkingArrow_cat C) C D (@adjunction_coimage_func C S t T T0 P Q)
  (@adjunction_image_func C S t T T0 P Q)) (@one_cat_coimage_image_comparison C S C1 t T T0 P Q))) (@fapp0 _ _
  (@comp_cat_con_fapp1_func B (Functor_cat WalkingArrow_cat C) C D (@adjunction_coimage_func C S t T T0 P Q)
  (@diagram_evaluation_at_func WalkingArrow_cat C walking_arrow_tgt)) (@one_cat_adjunction_coimage_to_target C S
  C1 t T T0 P Q)) (@omega_equiv_along_comp (Functor_cat B C) (@comp_cat_fapp0 B (Functor_cat
  WalkingArrow_cat C) C (@adjunction_coimage_func C S t T T0 P Q) D) (@comp_cat_fapp0 B (Functor_cat
  WalkingArrow_cat C) C (@adjunction_image_func C S t T T0 P Q) D) (@diagram_family_at_func B WalkingArrow_cat C D
  walking_arrow_tgt) (@fapp0 _ _ (@comp_cat_con_fapp1_func B (Functor_cat WalkingArrow_cat C) C D
  (@adjunction_coimage_func C S t T T0 P Q) (@adjunction_image_func C S t T T0 P Q))
  (@one_cat_coimage_image_comparison C S C1 t T T0 P Q)) (@fapp0 _ _ (@comp_cat_con_fapp1_func B (Functor_cat
  WalkingArrow_cat C) C D (@adjunction_image_func C S t T T0 P Q) (@diagram_evaluation_at_func WalkingArrow_cat C
  walking_arrow_tgt)) (@adjunction_image_inclusion C S t T T0 P Q)) (@one_cat_adjunction_normality_family B C S C1
  t T T0 P Q N D) (@one_cat_zero_cokernel_image_omega B C S C1 t T T0 P Q D z))
  (@one_cat_coimage_target_family_factor_path B C S C1 t T T0 P Q D);
