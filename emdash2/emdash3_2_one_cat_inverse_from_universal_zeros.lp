require open emdash.emdash3_2_one_cat_zero_cokernel_families;
require open emdash.emdash3_2_one_cat_zero_cokernel_covers;
require open emdash.emdash3_2_one_cat_coimage_cover_descent;

// Present the original zero kernel inclusion at its original coimage diagram.
symbol one_cat_kernel_zero_coimage_diagram_path [B C : Cat] [S : τ (@PreadditiveCategory C)] (C1 : τ (IsNCat
  (cat_succ cat_zero) C)) [t : τ (Obj C)] (T : τ (@TerminalObject C t)) (T0 : τ (@TerminalObject (Op_cat C) t)) (P
  : τ (@KernelAdjunctionStructure C S t T)) (Q : τ (@CokernelAdjunctionStructure C S t T0)) (D : τ (Functor B
  (Functor_cat WalkingArrow_cat C))) (zk : τ (@= (@Transf B C (@kernel_adjunction_family_func B C S t T P D)
  (@diagram_family_at_func B WalkingArrow_cat C D walking_arrow_src)) (@kernel_adjunction_family_inclusion_transf
  B C S t T P D) (@zero_arrow_family_zero_transf B C t T T0 (@kernel_adjunction_family_func B C S t T P D)
  (@diagram_family_at_func B WalkingArrow_cat C D walking_arrow_src))))
 : τ (@= (@Transf B C (@diagram_family_at_func B WalkingArrow_cat C (@comp_cat_fapp0 B (Functor_cat
  WalkingArrow_cat C) (Functor_cat WalkingArrow_cat C) (@kernel_adjunction_arrow_func C S t T P) D)
  walking_arrow_src) (@diagram_family_at_func B WalkingArrow_cat C (@comp_cat_fapp0 B (Functor_cat
  WalkingArrow_cat C) (Functor_cat WalkingArrow_cat C) (@kernel_adjunction_arrow_func C S t T P) D)
  walking_arrow_tgt)) (@diagram_family_transf B WalkingArrow_cat C (@comp_cat_fapp0 B (Functor_cat
  WalkingArrow_cat C) (Functor_cat WalkingArrow_cat C) (@kernel_adjunction_arrow_func C S t T P) D)
  walking_arrow_src walking_arrow_tgt walking_arrow_generator) (@zero_arrow_family_zero_transf B C t T T0
  (@diagram_family_at_func B WalkingArrow_cat C (@comp_cat_fapp0 B (Functor_cat WalkingArrow_cat C) (Functor_cat
  WalkingArrow_cat C) (@kernel_adjunction_arrow_func C S t T P) D) walking_arrow_src) (@diagram_family_at_func B
  WalkingArrow_cat C (@comp_cat_fapp0 B (Functor_cat WalkingArrow_cat C) (Functor_cat WalkingArrow_cat C)
  (@kernel_adjunction_arrow_func C S t T P) D) walking_arrow_tgt)))
≔ @eq_trans _ _ _ _ zk (@eq_trans _ _ _ _ (@eq_ap (@Transf B C (@diagram_family_at_func B WalkingArrow_cat C
  (@comp_cat_fapp0 B (Functor_cat WalkingArrow_cat C) (Functor_cat WalkingArrow_cat C)
  (@kernel_adjunction_arrow_func C S t T P) D) walking_arrow_src) (@Const_func B C t)) (@Transf B C
  (@diagram_family_at_func B WalkingArrow_cat C (@comp_cat_fapp0 B (Functor_cat WalkingArrow_cat C) (Functor_cat
  WalkingArrow_cat C) (@kernel_adjunction_arrow_func C S t T P) D) walking_arrow_src) (@diagram_family_at_func B
  WalkingArrow_cat C D walking_arrow_src)) (λ v : τ (@Transf B C (@diagram_family_at_func B WalkingArrow_cat C
  (@comp_cat_fapp0 B (Functor_cat WalkingArrow_cat C) (Functor_cat WalkingArrow_cat C)
  (@kernel_adjunction_arrow_func C S t T P) D) walking_arrow_src) (@Const_func B C t)), (@comp_fapp0 (Functor_cat
  B C) (@diagram_family_at_func B WalkingArrow_cat C (@comp_cat_fapp0 B (Functor_cat WalkingArrow_cat C)
  (Functor_cat WalkingArrow_cat C) (@kernel_adjunction_arrow_func C S t T P) D) walking_arrow_src) (@Const_func B
  C t) (@diagram_family_at_func B WalkingArrow_cat C D walking_arrow_src) (@diagram_family_transf B
  WalkingArrow_cat C (@comp_cat_fapp0 B C (Functor_cat WalkingArrow_cat C) (@initial_arrow_diagram_func C t T0)
  (@diagram_family_at_func B WalkingArrow_cat C D walking_arrow_src)) walking_arrow_src walking_arrow_tgt
  walking_arrow_generator) v)) (@diagram_family_transf B WalkingArrow_cat C (@comp_cat_fapp0 B C (Functor_cat
  WalkingArrow_cat C) (@terminal_arrow_diagram_func C t T) (@kernel_adjunction_family_func B C S t T P D))
  walking_arrow_src walking_arrow_tgt walking_arrow_generator) (@diagram_family_transf B WalkingArrow_cat C
  (@comp_cat_fapp0 B C (Functor_cat WalkingArrow_cat C) (@terminal_arrow_diagram_func C t T)
  (@diagram_family_at_func B WalkingArrow_cat C (@comp_cat_fapp0 B (Functor_cat WalkingArrow_cat C) (Functor_cat
  WalkingArrow_cat C) (@kernel_adjunction_arrow_func C S t T P) D) walking_arrow_src)) walking_arrow_src
  walking_arrow_tgt walking_arrow_generator) (@one_cat_terminal_family_arrow_path B C C1 t T
  (@diagram_family_at_func B WalkingArrow_cat C (@comp_cat_fapp0 B (Functor_cat WalkingArrow_cat C) (Functor_cat
  WalkingArrow_cat C) (@kernel_adjunction_arrow_func C S t T P) D) walking_arrow_src) (@diagram_family_transf B
  WalkingArrow_cat C (@comp_cat_fapp0 B C (Functor_cat WalkingArrow_cat C) (@terminal_arrow_diagram_func C t T)
  (@kernel_adjunction_family_func B C S t T P D)) walking_arrow_src walking_arrow_tgt walking_arrow_generator)))
  (@eq_ap (@Transf B C (@Const_func B C t) (@diagram_family_at_func B WalkingArrow_cat C (@comp_cat_fapp0 B
  (Functor_cat WalkingArrow_cat C) (Functor_cat WalkingArrow_cat C) (@kernel_adjunction_arrow_func C S t T P) D)
  walking_arrow_tgt)) (@Transf B C (@diagram_family_at_func B WalkingArrow_cat C (@comp_cat_fapp0 B (Functor_cat
  WalkingArrow_cat C) (Functor_cat WalkingArrow_cat C) (@kernel_adjunction_arrow_func C S t T P) D)
  walking_arrow_src) (@diagram_family_at_func B WalkingArrow_cat C (@comp_cat_fapp0 B (Functor_cat
  WalkingArrow_cat C) (Functor_cat WalkingArrow_cat C) (@kernel_adjunction_arrow_func C S t T P) D)
  walking_arrow_tgt)) (λ v : τ (@Transf B C (@Const_func B C t) (@diagram_family_at_func B WalkingArrow_cat C
  (@comp_cat_fapp0 B (Functor_cat WalkingArrow_cat C) (Functor_cat WalkingArrow_cat C)
  (@kernel_adjunction_arrow_func C S t T P) D) walking_arrow_tgt)), (@comp_fapp0 (Functor_cat B C)
  (@diagram_family_at_func B WalkingArrow_cat C (@comp_cat_fapp0 B (Functor_cat WalkingArrow_cat C) (Functor_cat
  WalkingArrow_cat C) (@kernel_adjunction_arrow_func C S t T P) D) walking_arrow_src) (@Const_func B C t)
  (@diagram_family_at_func B WalkingArrow_cat C (@comp_cat_fapp0 B (Functor_cat WalkingArrow_cat C) (Functor_cat
  WalkingArrow_cat C) (@kernel_adjunction_arrow_func C S t T P) D) walking_arrow_tgt) v (@diagram_family_transf B
  WalkingArrow_cat C (@comp_cat_fapp0 B C (Functor_cat WalkingArrow_cat C) (@terminal_arrow_diagram_func C t T)
  (@diagram_family_at_func B WalkingArrow_cat C (@comp_cat_fapp0 B (Functor_cat WalkingArrow_cat C) (Functor_cat
  WalkingArrow_cat C) (@kernel_adjunction_arrow_func C S t T P) D) walking_arrow_src)) walking_arrow_src
  walking_arrow_tgt walking_arrow_generator))) (@diagram_family_transf B WalkingArrow_cat C (@comp_cat_fapp0 B C
  (Functor_cat WalkingArrow_cat C) (@initial_arrow_diagram_func C t T0) (@diagram_family_at_func B
  WalkingArrow_cat C D walking_arrow_src)) walking_arrow_src walking_arrow_tgt walking_arrow_generator)
  (@diagram_family_transf B WalkingArrow_cat C (@comp_cat_fapp0 B C (Functor_cat WalkingArrow_cat C)
  (@initial_arrow_diagram_func C t T0) (@diagram_family_at_func B WalkingArrow_cat C (@comp_cat_fapp0 B
  (Functor_cat WalkingArrow_cat C) (Functor_cat WalkingArrow_cat C) (@kernel_adjunction_arrow_func C S t T P) D)
  walking_arrow_tgt)) walking_arrow_src walking_arrow_tgt walking_arrow_generator)
  (@one_cat_initial_family_arrow_path B C C1 t T0 (@diagram_family_at_func B WalkingArrow_cat C (@comp_cat_fapp0 B
  (Functor_cat WalkingArrow_cat C) (Functor_cat WalkingArrow_cat C) (@kernel_adjunction_arrow_func C S t T P) D)
  walking_arrow_tgt) (@diagram_family_transf B WalkingArrow_cat C (@comp_cat_fapp0 B C (Functor_cat
  WalkingArrow_cat C) (@initial_arrow_diagram_func C t T0) (@diagram_family_at_func B WalkingArrow_cat C D
  walking_arrow_src)) walking_arrow_src walking_arrow_tgt walking_arrow_generator))));

// Both original zero universal maps and original normality construct an inverse of the actual differential.
symbol one_cat_zero_kernel_cokernel_omega [B C : Cat] [S : τ (@PreadditiveCategory C)] (C1 : τ (IsNCat
  (cat_succ cat_zero) C)) [t : τ (Obj C)] (T : τ (@TerminalObject C t)) (T0 : τ (@TerminalObject (Op_cat C) t)) (P
  : τ (@KernelAdjunctionStructure C S t T)) (Q : τ (@CokernelAdjunctionStructure C S t T0)) (D : τ (Functor B
  (Functor_cat WalkingArrow_cat C))) (N : τ (@OneCatAdjunctionNormality C S C1 t T T0 P Q)) (zk : τ (@= (@Transf B
  C (@kernel_adjunction_family_func B C S t T P D) (@diagram_family_at_func B WalkingArrow_cat C D
  walking_arrow_src)) (@kernel_adjunction_family_inclusion_transf B C S t T P D) (@zero_arrow_family_zero_transf B
  C t T T0 (@kernel_adjunction_family_func B C S t T P D) (@diagram_family_at_func B WalkingArrow_cat C D
  walking_arrow_src)))) (zq : τ (@= (@Transf B C (@diagram_family_at_func B WalkingArrow_cat C D
  walking_arrow_tgt) (@cokernel_adjunction_family_func B C S t T0 Q D))
  (@cokernel_adjunction_family_projection_transf B C S t T0 Q D) (@zero_arrow_family_zero_transf B C t T T0
  (@diagram_family_at_func B WalkingArrow_cat C D walking_arrow_tgt) (@cokernel_adjunction_family_func B C S t T0
  Q D))))
 : τ (@OmegaEquivAlong (Functor_cat B C) (@diagram_family_at_func B WalkingArrow_cat C D walking_arrow_src)
  (@diagram_family_at_func B WalkingArrow_cat C D walking_arrow_tgt) (@diagram_family_transf B WalkingArrow_cat C
  D walking_arrow_src walking_arrow_tgt walking_arrow_generator))
≔ @omega_equiv_along_equal (Functor_cat B C) (@diagram_family_at_func B WalkingArrow_cat C D walking_arrow_src)
  (@diagram_family_at_func B WalkingArrow_cat C D walking_arrow_tgt) (@comp_fapp0 (Functor_cat B C)
  (@diagram_family_at_func B WalkingArrow_cat C D walking_arrow_src) (@comp_cat_fapp0 B (Functor_cat
  WalkingArrow_cat C) C (@adjunction_coimage_func C S t T T0 P Q) D) (@diagram_family_at_func B WalkingArrow_cat C
  D walking_arrow_tgt) (@fapp0 _ _ (@comp_cat_con_fapp1_func B (Functor_cat WalkingArrow_cat C) C D
  (@adjunction_coimage_func C S t T T0 P Q) (@diagram_evaluation_at_func WalkingArrow_cat C walking_arrow_tgt))
  (@one_cat_adjunction_coimage_to_target C S C1 t T T0 P Q)) (@cokernel_adjunction_family_projection_transf B C S
  t T0 Q (@comp_cat_fapp0 B (Functor_cat WalkingArrow_cat C) (Functor_cat WalkingArrow_cat C)
  (@kernel_adjunction_arrow_func C S t T P) D))) (@diagram_family_transf B WalkingArrow_cat C D walking_arrow_src
  walking_arrow_tgt walking_arrow_generator) (@omega_equiv_along_comp (Functor_cat B C) (@diagram_family_at_func B
  WalkingArrow_cat C D walking_arrow_src) (@comp_cat_fapp0 B (Functor_cat WalkingArrow_cat C) C
  (@adjunction_coimage_func C S t T T0 P Q) D) (@diagram_family_at_func B WalkingArrow_cat C D walking_arrow_tgt)
  (@cokernel_adjunction_family_projection_transf B C S t T0 Q (@comp_cat_fapp0 B (Functor_cat WalkingArrow_cat C)
  (Functor_cat WalkingArrow_cat C) (@kernel_adjunction_arrow_func C S t T P) D)) (@fapp0 _ _
  (@comp_cat_con_fapp1_func B (Functor_cat WalkingArrow_cat C) C D (@adjunction_coimage_func C S t T T0 P Q)
  (@diagram_evaluation_at_func WalkingArrow_cat C walking_arrow_tgt)) (@one_cat_adjunction_coimage_to_target C S
  C1 t T T0 P Q)) (@one_cat_zero_cokernel_omega B C S C1 t T T0 Q (@comp_cat_fapp0 B (Functor_cat
  WalkingArrow_cat C) (Functor_cat WalkingArrow_cat C) (@kernel_adjunction_arrow_func C S t T P) D)
  (@one_cat_kernel_zero_coimage_diagram_path B C S C1 t T T0 P Q D zk)) (@one_cat_zero_cokernel_cover_omega
  B C S C1 t T T0 P Q N D zq)) (@one_cat_coimage_family_factor_path B C S C1 t T T0 P Q D);
