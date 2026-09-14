require open emdash.emdash3_2_one_cat_zero_cokernel_covers;
require open emdash.emdash3_2_one_cat_cokernel_family_reconstruction;
require open emdash.emdash3_2_omega_equiv_cancellation_paths;

// Restriction retains the original quotient of the original kernel diagram.
symbol one_cat_coimage_family_quotient_path [B C : Cat] [S : τ (@PreadditiveCategory C)] (C1 : τ (IsNCat
  (cat_succ cat_zero) C)) [t : τ (Obj C)] (T : τ (@TerminalObject C t)) (T0 : τ (@TerminalObject (Op_cat C) t)) (P
  : τ (@KernelAdjunctionStructure C S t T)) (Q : τ (@CokernelAdjunctionStructure C S t T0)) (D : τ (Functor B
  (Functor_cat WalkingArrow_cat C)))
 : τ (@= (@Transf B C (@diagram_family_at_func B WalkingArrow_cat C D walking_arrow_src) (@comp_cat_fapp0 B
  (Functor_cat WalkingArrow_cat C) C (@adjunction_coimage_func C S t T T0 P Q) D))
  (@cokernel_adjunction_family_projection_transf B C S t T0 Q (@comp_cat_fapp0 B (Functor_cat WalkingArrow_cat C)
  (Functor_cat WalkingArrow_cat C) (@kernel_adjunction_arrow_func C S t T P) D)) (@fapp0 _ _
  (@comp_cat_con_fapp1_func B (Functor_cat WalkingArrow_cat C) C D (@diagram_evaluation_at_func WalkingArrow_cat C
  walking_arrow_src) (@adjunction_coimage_func C S t T T0 P Q)) (@cokernel_adjunction_family_projection_transf
  (Functor_cat WalkingArrow_cat C) C S t T0 Q (@kernel_adjunction_arrow_func C S t T P))))
≔ @one_cat_diagram_family_transf_reindex_path B (Functor_cat WalkingArrow_cat C) WalkingArrow_cat C C1
  (@comp_cat_fapp0 (Functor_cat WalkingArrow_cat C) (Functor_cat WalkingArrow_cat C) (Functor_cat WalkingArrow_cat
  C) (@cokernel_adjunction_arrow_func C S t T0 Q) (@kernel_adjunction_arrow_func C S t T P)) D walking_arrow_src
  walking_arrow_tgt walking_arrow_generator;

// The original coimage factor and quotient reconstruct the entire original differential.
symbol one_cat_coimage_family_factor_path [B C : Cat] [S : τ (@PreadditiveCategory C)] (C1 : τ (IsNCat
  (cat_succ cat_zero) C)) [t : τ (Obj C)] (T : τ (@TerminalObject C t)) (T0 : τ (@TerminalObject (Op_cat C) t)) (P
  : τ (@KernelAdjunctionStructure C S t T)) (Q : τ (@CokernelAdjunctionStructure C S t T0)) (D : τ (Functor B
  (Functor_cat WalkingArrow_cat C)))
 : τ (@= (@Transf B C (@diagram_family_at_func B WalkingArrow_cat C D walking_arrow_src) (@diagram_family_at_func
  B WalkingArrow_cat C D walking_arrow_tgt)) (@comp_fapp0 (Functor_cat B C) (@diagram_family_at_func B
  WalkingArrow_cat C D walking_arrow_src) (@comp_cat_fapp0 B (Functor_cat WalkingArrow_cat C) C
  (@adjunction_coimage_func C S t T T0 P Q) D) (@diagram_family_at_func B WalkingArrow_cat C D walking_arrow_tgt)
  (@fapp0 _ _ (@comp_cat_con_fapp1_func B (Functor_cat WalkingArrow_cat C) C D (@adjunction_coimage_func C S t T
  T0 P Q) (@diagram_evaluation_at_func WalkingArrow_cat C walking_arrow_tgt))
  (@one_cat_adjunction_coimage_to_target C S C1 t T T0 P Q)) (@cokernel_adjunction_family_projection_transf B C S
  t T0 Q (@comp_cat_fapp0 B (Functor_cat WalkingArrow_cat C) (Functor_cat WalkingArrow_cat C)
  (@kernel_adjunction_arrow_func C S t T P) D))) (@diagram_family_transf B WalkingArrow_cat C D walking_arrow_src
  walking_arrow_tgt walking_arrow_generator))
≔ @eq_trans _ _ _ _ (@eq_ap (@Transf B C (@diagram_family_at_func B WalkingArrow_cat C D walking_arrow_src)
  (@comp_cat_fapp0 B (Functor_cat WalkingArrow_cat C) C (@adjunction_coimage_func C S t T T0 P Q) D)) (@Transf B C
  (@diagram_family_at_func B WalkingArrow_cat C D walking_arrow_src) (@diagram_family_at_func B WalkingArrow_cat C
  D walking_arrow_tgt)) (λ a : τ (@Transf B C (@diagram_family_at_func B WalkingArrow_cat C D walking_arrow_src)
  (@comp_cat_fapp0 B (Functor_cat WalkingArrow_cat C) C (@adjunction_coimage_func C S t T T0 P Q) D)),
  (@comp_fapp0 (Functor_cat B C) (@diagram_family_at_func B WalkingArrow_cat C D walking_arrow_src)
  (@comp_cat_fapp0 B (Functor_cat WalkingArrow_cat C) C (@adjunction_coimage_func C S t T T0 P Q) D)
  (@diagram_family_at_func B WalkingArrow_cat C D walking_arrow_tgt) (@fapp0 _ _ (@comp_cat_con_fapp1_func B
  (Functor_cat WalkingArrow_cat C) C D (@adjunction_coimage_func C S t T T0 P Q) (@diagram_evaluation_at_func
  WalkingArrow_cat C walking_arrow_tgt)) (@one_cat_adjunction_coimage_to_target C S C1 t T T0 P Q)) a))
  (@cokernel_adjunction_family_projection_transf B C S t T0 Q (@comp_cat_fapp0 B (Functor_cat WalkingArrow_cat C)
  (Functor_cat WalkingArrow_cat C) (@kernel_adjunction_arrow_func C S t T P) D)) (@fapp0 _ _
  (@comp_cat_con_fapp1_func B (Functor_cat WalkingArrow_cat C) C D (@diagram_evaluation_at_func WalkingArrow_cat C
  walking_arrow_src) (@adjunction_coimage_func C S t T T0 P Q)) (@cokernel_adjunction_family_projection_transf
  (Functor_cat WalkingArrow_cat C) C S t T0 Q (@kernel_adjunction_arrow_func C S t T P)))
  (@one_cat_coimage_family_quotient_path B C S C1 t T T0 P Q D)) (@eq_trans _ _ _ _ (@eq_sym _ _ _
  (@prewhisker_comp_path B (Functor_cat WalkingArrow_cat C) C D (@diagram_evaluation_at_func WalkingArrow_cat C
  walking_arrow_src) (@adjunction_coimage_func C S t T T0 P Q) (@diagram_evaluation_at_func WalkingArrow_cat C
  walking_arrow_tgt) (@cokernel_adjunction_family_projection_transf (Functor_cat WalkingArrow_cat C) C S t T0 Q
  (@kernel_adjunction_arrow_func C S t T P)) (@one_cat_adjunction_coimage_to_target C S C1 t T T0 P Q)))
  (@eq_trans _ _ _ _ (@eq_ap (@Transf (Functor_cat WalkingArrow_cat C) C (@diagram_evaluation_at_func
  WalkingArrow_cat C walking_arrow_src) (@diagram_evaluation_at_func WalkingArrow_cat C walking_arrow_tgt))
  (@Transf B C (@diagram_family_at_func B WalkingArrow_cat C D walking_arrow_src) (@diagram_family_at_func B
  WalkingArrow_cat C D walking_arrow_tgt)) (λ a : τ (@Transf (Functor_cat WalkingArrow_cat C) C
  (@diagram_evaluation_at_func WalkingArrow_cat C walking_arrow_src) (@diagram_evaluation_at_func WalkingArrow_cat
  C walking_arrow_tgt)), (@fapp0 _ _ (@comp_cat_con_fapp1_func B (Functor_cat WalkingArrow_cat C) C D
  (@diagram_evaluation_at_func WalkingArrow_cat C walking_arrow_src) (@diagram_evaluation_at_func WalkingArrow_cat
  C walking_arrow_tgt)) a)) (@comp_fapp0 (Functor_cat (Functor_cat WalkingArrow_cat C) C)
  (@diagram_evaluation_at_func WalkingArrow_cat C walking_arrow_src) (@adjunction_coimage_func C S t T T0 P Q)
  (@diagram_evaluation_at_func WalkingArrow_cat C walking_arrow_tgt) (@one_cat_adjunction_coimage_to_target C S C1
  t T T0 P Q) (@cokernel_adjunction_family_projection_transf (Functor_cat WalkingArrow_cat C) C S t T0 Q
  (@kernel_adjunction_arrow_func C S t T P))) (@diagram_evaluation_transf WalkingArrow_cat C walking_arrow_src
  walking_arrow_tgt walking_arrow_generator) (@one_cat_coimage_factor_ambient_path C S C1 t T T0 P Q)) (@eq_sym _
  _ _ (@one_cat_diagram_family_transf_whisker_path B WalkingArrow_cat C C1 D walking_arrow_src walking_arrow_tgt
  walking_arrow_generator))));

// Whole terminal uniqueness presents the original kernel-annihilation at its original graph.
symbol one_cat_coimage_family_input_zero [B C : Cat] [S : τ (@PreadditiveCategory C)] (C1 : τ (IsNCat
  (cat_succ cat_zero) C)) [t : τ (Obj C)] (T : τ (@TerminalObject C t)) (T0 : τ (@TerminalObject (Op_cat C) t)) (P
  : τ (@KernelAdjunctionStructure C S t T)) (Q : τ (@CokernelAdjunctionStructure C S t T0)) (D : τ (Functor B
  (Functor_cat WalkingArrow_cat C))) (V : τ (Functor B C)) (u : τ (@Transf B C (@diagram_family_at_func B
  WalkingArrow_cat C D walking_arrow_src) V)) (z : τ (@= (@Transf B C (@comp_cat_fapp0 B (Functor_cat
  WalkingArrow_cat C) C (@kernel_adjunction_func C S t T P) D) V) (@comp_fapp0 (Functor_cat B C) (@comp_cat_fapp0
  B (Functor_cat WalkingArrow_cat C) C (@kernel_adjunction_func C S t T P) D) (@diagram_family_at_func B
  WalkingArrow_cat C D walking_arrow_src) V u (@kernel_adjunction_family_inclusion_transf B C S t T P D))
  (@zero_arrow_family_zero_transf B C t T T0 (@comp_cat_fapp0 B (Functor_cat WalkingArrow_cat C) C
  (@kernel_adjunction_func C S t T P) D) V)))
 : τ (@= (@Transf B C (@diagram_family_at_func B WalkingArrow_cat C (@comp_cat_fapp0 B (Functor_cat
  WalkingArrow_cat C) (Functor_cat WalkingArrow_cat C) (@kernel_adjunction_arrow_func C S t T P) D)
  walking_arrow_src) V) (@comp_fapp0 (Functor_cat B C) (@diagram_family_at_func B WalkingArrow_cat C
  (@comp_cat_fapp0 B (Functor_cat WalkingArrow_cat C) (Functor_cat WalkingArrow_cat C)
  (@kernel_adjunction_arrow_func C S t T P) D) walking_arrow_src) (@diagram_family_at_func B WalkingArrow_cat C
  (@comp_cat_fapp0 B (Functor_cat WalkingArrow_cat C) (Functor_cat WalkingArrow_cat C)
  (@kernel_adjunction_arrow_func C S t T P) D) walking_arrow_tgt) V u (@diagram_family_transf B WalkingArrow_cat C
  (@comp_cat_fapp0 B (Functor_cat WalkingArrow_cat C) (Functor_cat WalkingArrow_cat C)
  (@kernel_adjunction_arrow_func C S t T P) D) walking_arrow_src walking_arrow_tgt walking_arrow_generator))
  (@zero_arrow_family_zero_transf B C t T T0 (@diagram_family_at_func B WalkingArrow_cat C (@comp_cat_fapp0 B
  (Functor_cat WalkingArrow_cat C) (Functor_cat WalkingArrow_cat C) (@kernel_adjunction_arrow_func C S t T P) D)
  walking_arrow_src) V))
≔ @eq_trans _ _ _ _ z (@eq_ap (@Transf B C (@diagram_family_at_func B WalkingArrow_cat C (@comp_cat_fapp0 B
  (Functor_cat WalkingArrow_cat C) (Functor_cat WalkingArrow_cat C) (@kernel_adjunction_arrow_func C S t T P) D)
  walking_arrow_src) (@Const_func B C t)) (@Transf B C (@diagram_family_at_func B WalkingArrow_cat C
  (@comp_cat_fapp0 B (Functor_cat WalkingArrow_cat C) (Functor_cat WalkingArrow_cat C)
  (@kernel_adjunction_arrow_func C S t T P) D) walking_arrow_src) V) (λ a : τ (@Transf B C
  (@diagram_family_at_func B WalkingArrow_cat C (@comp_cat_fapp0 B (Functor_cat WalkingArrow_cat C) (Functor_cat
  WalkingArrow_cat C) (@kernel_adjunction_arrow_func C S t T P) D) walking_arrow_src) (@Const_func B C t)),
  (@comp_fapp0 (Functor_cat B C) (@diagram_family_at_func B WalkingArrow_cat C (@comp_cat_fapp0 B (Functor_cat
  WalkingArrow_cat C) (Functor_cat WalkingArrow_cat C) (@kernel_adjunction_arrow_func C S t T P) D)
  walking_arrow_src) (@Const_func B C t) V (@diagram_family_transf B WalkingArrow_cat C (@comp_cat_fapp0 B C
  (Functor_cat WalkingArrow_cat C) (@initial_arrow_diagram_func C t T0) V) walking_arrow_src walking_arrow_tgt
  walking_arrow_generator) a)) (@diagram_family_transf B WalkingArrow_cat C (@comp_cat_fapp0 B C (Functor_cat
  WalkingArrow_cat C) (@terminal_arrow_diagram_func C t T) (@comp_cat_fapp0 B (Functor_cat WalkingArrow_cat C) C
  (@kernel_adjunction_func C S t T P) D)) walking_arrow_src walking_arrow_tgt walking_arrow_generator)
  (@diagram_family_transf B WalkingArrow_cat C (@comp_cat_fapp0 B C (Functor_cat WalkingArrow_cat C)
  (@terminal_arrow_diagram_func C t T) (@diagram_family_at_func B WalkingArrow_cat C (@comp_cat_fapp0 B
  (Functor_cat WalkingArrow_cat C) (Functor_cat WalkingArrow_cat C) (@kernel_adjunction_arrow_func C S t T P) D)
  walking_arrow_src)) walking_arrow_src walking_arrow_tgt walking_arrow_generator)
  (@one_cat_terminal_family_arrow_path B C C1 t T (@diagram_family_at_func B WalkingArrow_cat C (@comp_cat_fapp0 B
  (Functor_cat WalkingArrow_cat C) (Functor_cat WalkingArrow_cat C) (@kernel_adjunction_arrow_func C S t T P) D)
  walking_arrow_src) (@diagram_family_transf B WalkingArrow_cat C (@comp_cat_fapp0 B C (Functor_cat
  WalkingArrow_cat C) (@terminal_arrow_diagram_func C t T) (@comp_cat_fapp0 B (Functor_cat WalkingArrow_cat C) C
  (@kernel_adjunction_func C S t T P) D)) walking_arrow_src walking_arrow_tgt walking_arrow_generator)));

// Descend through Q at the original restricted kernel-arrow family.
symbol one_cat_coimage_family_descent [B C : Cat] [S : τ (@PreadditiveCategory C)] (C1 : τ (IsNCat (cat_succ
  cat_zero) C)) [t : τ (Obj C)] (T : τ (@TerminalObject C t)) (T0 : τ (@TerminalObject (Op_cat C) t)) (P : τ
  (@KernelAdjunctionStructure C S t T)) (Q : τ (@CokernelAdjunctionStructure C S t T0)) (D : τ (Functor B
  (Functor_cat WalkingArrow_cat C))) (V : τ (Functor B C)) (u : τ (@Transf B C (@diagram_family_at_func B
  WalkingArrow_cat C D walking_arrow_src) V)) (z : τ (@= (@Transf B C (@comp_cat_fapp0 B (Functor_cat
  WalkingArrow_cat C) C (@kernel_adjunction_func C S t T P) D) V) (@comp_fapp0 (Functor_cat B C) (@comp_cat_fapp0
  B (Functor_cat WalkingArrow_cat C) C (@kernel_adjunction_func C S t T P) D) (@diagram_family_at_func B
  WalkingArrow_cat C D walking_arrow_src) V u (@kernel_adjunction_family_inclusion_transf B C S t T P D))
  (@zero_arrow_family_zero_transf B C t T T0 (@comp_cat_fapp0 B (Functor_cat WalkingArrow_cat C) C
  (@kernel_adjunction_func C S t T P) D) V)))
 : τ (@Transf B C (@comp_cat_fapp0 B (Functor_cat WalkingArrow_cat C) C (@adjunction_coimage_func C S t T T0 P Q)
  D) V)
≔ @one_cat_cokernel_family_descent B C S C1 t T T0 Q (@comp_cat_fapp0 B (Functor_cat WalkingArrow_cat C)
  (Functor_cat WalkingArrow_cat C) (@kernel_adjunction_arrow_func C S t T P) D) V u
  (@one_cat_coimage_family_input_zero B C S C1 t T T0 P Q D V u z);

// The same original quotient reconstructs the whole input.
symbol one_cat_coimage_family_descent_reconstruction [B C : Cat] [S : τ (@PreadditiveCategory C)] (C1 : τ
  (IsNCat (cat_succ cat_zero) C)) [t : τ (Obj C)] (T : τ (@TerminalObject C t)) (T0 : τ (@TerminalObject (Op_cat
  C) t)) (P : τ (@KernelAdjunctionStructure C S t T)) (Q : τ (@CokernelAdjunctionStructure C S t T0)) (D : τ
  (Functor B (Functor_cat WalkingArrow_cat C))) (V : τ (Functor B C)) (u : τ (@Transf B C (@diagram_family_at_func
  B WalkingArrow_cat C D walking_arrow_src) V)) (z : τ (@= (@Transf B C (@comp_cat_fapp0 B (Functor_cat
  WalkingArrow_cat C) C (@kernel_adjunction_func C S t T P) D) V) (@comp_fapp0 (Functor_cat B C) (@comp_cat_fapp0
  B (Functor_cat WalkingArrow_cat C) C (@kernel_adjunction_func C S t T P) D) (@diagram_family_at_func B
  WalkingArrow_cat C D walking_arrow_src) V u (@kernel_adjunction_family_inclusion_transf B C S t T P D))
  (@zero_arrow_family_zero_transf B C t T T0 (@comp_cat_fapp0 B (Functor_cat WalkingArrow_cat C) C
  (@kernel_adjunction_func C S t T P) D) V)))
 : τ (@= (@Transf B C (@diagram_family_at_func B WalkingArrow_cat C D walking_arrow_src) V) (@comp_fapp0
  (Functor_cat B C) (@diagram_family_at_func B WalkingArrow_cat C D walking_arrow_src) (@comp_cat_fapp0 B
  (Functor_cat WalkingArrow_cat C) C (@adjunction_coimage_func C S t T T0 P Q) D) V
  (@one_cat_coimage_family_descent B C S C1 t T T0 P Q D V u z)
  (@cokernel_adjunction_family_projection_transf B C S t T0 Q (@comp_cat_fapp0 B (Functor_cat WalkingArrow_cat C)
  (Functor_cat WalkingArrow_cat C) (@kernel_adjunction_arrow_func C S t T P) D))) u)
≔ @one_cat_cokernel_family_descent_ambient_reconstruction B C S C1 t T T0 Q (@comp_cat_fapp0 B (Functor_cat
  WalkingArrow_cat C) (Functor_cat WalkingArrow_cat C) (@kernel_adjunction_arrow_func C S t T P) D) V u
  (@one_cat_coimage_family_input_zero B C S C1 t T T0 P Q D V u z);

// The selected whole cover inverse recovers the original coimage quotient.
symbol one_cat_coimage_cover_inverse_factor_path [B C : Cat] [S : τ (@PreadditiveCategory C)] (C1 : τ
  (IsNCat (cat_succ cat_zero) C)) [t : τ (Obj C)] (T : τ (@TerminalObject C t)) (T0 : τ (@TerminalObject (Op_cat
  C) t)) (P : τ (@KernelAdjunctionStructure C S t T)) (Q : τ (@CokernelAdjunctionStructure C S t T0)) (D : τ
  (Functor B (Functor_cat WalkingArrow_cat C))) (E : τ (@OmegaEquivAlong (Functor_cat B C) (@comp_cat_fapp0 B
  (Functor_cat WalkingArrow_cat C) C (@adjunction_coimage_func C S t T T0 P Q) D) (@diagram_family_at_func B
  WalkingArrow_cat C D walking_arrow_tgt) (@fapp0 _ _ (@comp_cat_con_fapp1_func B (Functor_cat WalkingArrow_cat C)
  C D (@adjunction_coimage_func C S t T T0 P Q) (@diagram_evaluation_at_func WalkingArrow_cat C
  walking_arrow_tgt)) (@one_cat_adjunction_coimage_to_target C S C1 t T T0 P Q))))
 : τ (@= (@Transf B C (@diagram_family_at_func B WalkingArrow_cat C D walking_arrow_src) (@comp_cat_fapp0 B
  (Functor_cat WalkingArrow_cat C) C (@adjunction_coimage_func C S t T T0 P Q) D)) (@comp_fapp0 (Functor_cat B C)
  (@diagram_family_at_func B WalkingArrow_cat C D walking_arrow_src) (@diagram_family_at_func B WalkingArrow_cat C
  D walking_arrow_tgt) (@comp_cat_fapp0 B (Functor_cat WalkingArrow_cat C) C (@adjunction_coimage_func C S t T T0
  P Q) D) (@omega_equiv_along_left_inv (Functor_cat B C) (@comp_cat_fapp0 B (Functor_cat WalkingArrow_cat C) C
  (@adjunction_coimage_func C S t T T0 P Q) D) (@diagram_family_at_func B WalkingArrow_cat C D walking_arrow_tgt)
  (@fapp0 _ _ (@comp_cat_con_fapp1_func B (Functor_cat WalkingArrow_cat C) C D (@adjunction_coimage_func C S t T
  T0 P Q) (@diagram_evaluation_at_func WalkingArrow_cat C walking_arrow_tgt))
  (@one_cat_adjunction_coimage_to_target C S C1 t T T0 P Q)) E) (@diagram_family_transf B WalkingArrow_cat C D
  walking_arrow_src walking_arrow_tgt walking_arrow_generator)) (@cokernel_adjunction_family_projection_transf B C
  S t T0 Q (@comp_cat_fapp0 B (Functor_cat WalkingArrow_cat C) (Functor_cat WalkingArrow_cat C)
  (@kernel_adjunction_arrow_func C S t T P) D)))
≔ @eq_trans _ _ _ _ (@eq_ap (@Transf B C (@diagram_family_at_func B WalkingArrow_cat C D walking_arrow_src)
  (@diagram_family_at_func B WalkingArrow_cat C D walking_arrow_tgt)) (@Transf B C (@diagram_family_at_func B
  WalkingArrow_cat C D walking_arrow_src) (@comp_cat_fapp0 B (Functor_cat WalkingArrow_cat C) C
  (@adjunction_coimage_func C S t T T0 P Q) D)) (λ a : τ (@Transf B C (@diagram_family_at_func B WalkingArrow_cat
  C D walking_arrow_src) (@diagram_family_at_func B WalkingArrow_cat C D walking_arrow_tgt)), (@comp_fapp0
  (Functor_cat B C) (@diagram_family_at_func B WalkingArrow_cat C D walking_arrow_src) (@diagram_family_at_func B
  WalkingArrow_cat C D walking_arrow_tgt) (@comp_cat_fapp0 B (Functor_cat WalkingArrow_cat C) C
  (@adjunction_coimage_func C S t T T0 P Q) D) (@omega_equiv_along_left_inv (Functor_cat B C) (@comp_cat_fapp0 B
  (Functor_cat WalkingArrow_cat C) C (@adjunction_coimage_func C S t T T0 P Q) D) (@diagram_family_at_func B
  WalkingArrow_cat C D walking_arrow_tgt) (@fapp0 _ _ (@comp_cat_con_fapp1_func B (Functor_cat WalkingArrow_cat C)
  C D (@adjunction_coimage_func C S t T T0 P Q) (@diagram_evaluation_at_func WalkingArrow_cat C
  walking_arrow_tgt)) (@one_cat_adjunction_coimage_to_target C S C1 t T T0 P Q)) E) a)) (@diagram_family_transf B
  WalkingArrow_cat C D walking_arrow_src walking_arrow_tgt walking_arrow_generator) (@comp_fapp0 (Functor_cat B C)
  (@diagram_family_at_func B WalkingArrow_cat C D walking_arrow_src) (@comp_cat_fapp0 B (Functor_cat
  WalkingArrow_cat C) C (@adjunction_coimage_func C S t T T0 P Q) D) (@diagram_family_at_func B WalkingArrow_cat C
  D walking_arrow_tgt) (@fapp0 _ _ (@comp_cat_con_fapp1_func B (Functor_cat WalkingArrow_cat C) C D
  (@adjunction_coimage_func C S t T T0 P Q) (@diagram_evaluation_at_func WalkingArrow_cat C walking_arrow_tgt))
  (@one_cat_adjunction_coimage_to_target C S C1 t T T0 P Q)) (@cokernel_adjunction_family_projection_transf B C S
  t T0 Q (@comp_cat_fapp0 B (Functor_cat WalkingArrow_cat C) (Functor_cat WalkingArrow_cat C)
  (@kernel_adjunction_arrow_func C S t T P) D))) (@eq_sym _ _ _ (@one_cat_coimage_family_factor_path B C S
  C1 t T T0 P Q D))) (@eq_trans _ _ _ _ (@comp_assoc (Functor_cat B C) (@diagram_family_at_func B WalkingArrow_cat
  C D walking_arrow_src) (@comp_cat_fapp0 B (Functor_cat WalkingArrow_cat C) C (@adjunction_coimage_func C S t T
  T0 P Q) D) (@diagram_family_at_func B WalkingArrow_cat C D walking_arrow_tgt) (@comp_cat_fapp0 B (Functor_cat
  WalkingArrow_cat C) C (@adjunction_coimage_func C S t T T0 P Q) D) (@omega_equiv_along_left_inv (Functor_cat B
  C) (@comp_cat_fapp0 B (Functor_cat WalkingArrow_cat C) C (@adjunction_coimage_func C S t T T0 P Q) D)
  (@diagram_family_at_func B WalkingArrow_cat C D walking_arrow_tgt) (@fapp0 _ _ (@comp_cat_con_fapp1_func B
  (Functor_cat WalkingArrow_cat C) C D (@adjunction_coimage_func C S t T T0 P Q) (@diagram_evaluation_at_func
  WalkingArrow_cat C walking_arrow_tgt)) (@one_cat_adjunction_coimage_to_target C S C1 t T T0 P Q)) E) (@fapp0 _ _
  (@comp_cat_con_fapp1_func B (Functor_cat WalkingArrow_cat C) C D (@adjunction_coimage_func C S t T T0 P Q)
  (@diagram_evaluation_at_func WalkingArrow_cat C walking_arrow_tgt)) (@one_cat_adjunction_coimage_to_target C S
  C1 t T T0 P Q)) (@cokernel_adjunction_family_projection_transf B C S t T0 Q (@comp_cat_fapp0 B (Functor_cat
  WalkingArrow_cat C) (Functor_cat WalkingArrow_cat C) (@kernel_adjunction_arrow_func C S t T P) D))) (@eq_ap
  (@Transf B C (@comp_cat_fapp0 B (Functor_cat WalkingArrow_cat C) C (@adjunction_coimage_func C S t T T0 P Q) D)
  (@comp_cat_fapp0 B (Functor_cat WalkingArrow_cat C) C (@adjunction_coimage_func C S t T T0 P Q) D)) (@Transf B C
  (@diagram_family_at_func B WalkingArrow_cat C D walking_arrow_src) (@comp_cat_fapp0 B (Functor_cat
  WalkingArrow_cat C) C (@adjunction_coimage_func C S t T T0 P Q) D)) (λ a : τ (@Transf B C (@comp_cat_fapp0 B
  (Functor_cat WalkingArrow_cat C) C (@adjunction_coimage_func C S t T T0 P Q) D) (@comp_cat_fapp0 B (Functor_cat
  WalkingArrow_cat C) C (@adjunction_coimage_func C S t T T0 P Q) D)), (@comp_fapp0 (Functor_cat B C)
  (@diagram_family_at_func B WalkingArrow_cat C D walking_arrow_src) (@comp_cat_fapp0 B (Functor_cat
  WalkingArrow_cat C) C (@adjunction_coimage_func C S t T T0 P Q) D) (@comp_cat_fapp0 B (Functor_cat
  WalkingArrow_cat C) C (@adjunction_coimage_func C S t T T0 P Q) D) a
  (@cokernel_adjunction_family_projection_transf B C S t T0 Q (@comp_cat_fapp0 B (Functor_cat WalkingArrow_cat C)
  (Functor_cat WalkingArrow_cat C) (@kernel_adjunction_arrow_func C S t T P) D)))) (@comp_fapp0 (Functor_cat B C)
  (@comp_cat_fapp0 B (Functor_cat WalkingArrow_cat C) C (@adjunction_coimage_func C S t T T0 P Q) D)
  (@diagram_family_at_func B WalkingArrow_cat C D walking_arrow_tgt) (@comp_cat_fapp0 B (Functor_cat
  WalkingArrow_cat C) C (@adjunction_coimage_func C S t T T0 P Q) D) (@omega_equiv_along_left_inv (Functor_cat B
  C) (@comp_cat_fapp0 B (Functor_cat WalkingArrow_cat C) C (@adjunction_coimage_func C S t T T0 P Q) D)
  (@diagram_family_at_func B WalkingArrow_cat C D walking_arrow_tgt) (@fapp0 _ _ (@comp_cat_con_fapp1_func B
  (Functor_cat WalkingArrow_cat C) C D (@adjunction_coimage_func C S t T T0 P Q) (@diagram_evaluation_at_func
  WalkingArrow_cat C walking_arrow_tgt)) (@one_cat_adjunction_coimage_to_target C S C1 t T T0 P Q)) E) (@fapp0 _ _
  (@comp_cat_con_fapp1_func B (Functor_cat WalkingArrow_cat C) C D (@adjunction_coimage_func C S t T T0 P Q)
  (@diagram_evaluation_at_func WalkingArrow_cat C walking_arrow_tgt)) (@one_cat_adjunction_coimage_to_target C S
  C1 t T T0 P Q))) (@id (Functor_cat B C) (@comp_cat_fapp0 B (Functor_cat WalkingArrow_cat C) C
  (@adjunction_coimage_func C S t T T0 P Q) D)) (@omega_equiv_along_left_law (Functor_cat B C) (@comp_cat_fapp0 B
  (Functor_cat WalkingArrow_cat C) C (@adjunction_coimage_func C S t T T0 P Q) D) (@diagram_family_at_func B
  WalkingArrow_cat C D walking_arrow_tgt) (@fapp0 _ _ (@comp_cat_con_fapp1_func B (Functor_cat WalkingArrow_cat C)
  C D (@adjunction_coimage_func C S t T T0 P Q) (@diagram_evaluation_at_func WalkingArrow_cat C
  walking_arrow_tgt)) (@one_cat_adjunction_coimage_to_target C S C1 t T T0 P Q)) E)));

// Compose the original cokernel descent with the proved cover inverse.
symbol one_cat_coimage_cover_descent [B C : Cat] [S : τ (@PreadditiveCategory C)] (C1 : τ (IsNCat (cat_succ
  cat_zero) C)) [t : τ (Obj C)] (T : τ (@TerminalObject C t)) (T0 : τ (@TerminalObject (Op_cat C) t)) (P : τ
  (@KernelAdjunctionStructure C S t T)) (Q : τ (@CokernelAdjunctionStructure C S t T0)) (D : τ (Functor B
  (Functor_cat WalkingArrow_cat C))) (E : τ (@OmegaEquivAlong (Functor_cat B C) (@comp_cat_fapp0 B (Functor_cat
  WalkingArrow_cat C) C (@adjunction_coimage_func C S t T T0 P Q) D) (@diagram_family_at_func B WalkingArrow_cat C
  D walking_arrow_tgt) (@fapp0 _ _ (@comp_cat_con_fapp1_func B (Functor_cat WalkingArrow_cat C) C D
  (@adjunction_coimage_func C S t T T0 P Q) (@diagram_evaluation_at_func WalkingArrow_cat C walking_arrow_tgt))
  (@one_cat_adjunction_coimage_to_target C S C1 t T T0 P Q)))) (V : τ (Functor B C)) (u : τ (@Transf B C
  (@diagram_family_at_func B WalkingArrow_cat C D walking_arrow_src) V)) (z : τ (@= (@Transf B C (@comp_cat_fapp0
  B (Functor_cat WalkingArrow_cat C) C (@kernel_adjunction_func C S t T P) D) V) (@comp_fapp0 (Functor_cat B C)
  (@comp_cat_fapp0 B (Functor_cat WalkingArrow_cat C) C (@kernel_adjunction_func C S t T P) D)
  (@diagram_family_at_func B WalkingArrow_cat C D walking_arrow_src) V u
  (@kernel_adjunction_family_inclusion_transf B C S t T P D)) (@zero_arrow_family_zero_transf B C t T T0
  (@comp_cat_fapp0 B (Functor_cat WalkingArrow_cat C) C (@kernel_adjunction_func C S t T P) D) V)))
 : τ (@Transf B C (@diagram_family_at_func B WalkingArrow_cat C D walking_arrow_tgt) V)
≔ (@comp_fapp0 (Functor_cat B C) (@diagram_family_at_func B WalkingArrow_cat C D walking_arrow_tgt)
  (@comp_cat_fapp0 B (Functor_cat WalkingArrow_cat C) C (@adjunction_coimage_func C S t T T0 P Q) D) V
  (@one_cat_coimage_family_descent B C S C1 t T T0 P Q D V u z) (@omega_equiv_along_left_inv (Functor_cat B
  C) (@comp_cat_fapp0 B (Functor_cat WalkingArrow_cat C) C (@adjunction_coimage_func C S t T T0 P Q) D)
  (@diagram_family_at_func B WalkingArrow_cat C D walking_arrow_tgt) (@fapp0 _ _ (@comp_cat_con_fapp1_func B
  (Functor_cat WalkingArrow_cat C) C D (@adjunction_coimage_func C S t T T0 P Q) (@diagram_evaluation_at_func
  WalkingArrow_cat C walking_arrow_tgt)) (@one_cat_adjunction_coimage_to_target C S C1 t T T0 P Q)) E));

// Descent reconstructs the original whole map after the original differential.
symbol one_cat_coimage_cover_descent_reconstruction [B C : Cat] [S : τ (@PreadditiveCategory C)] (C1 : τ
  (IsNCat (cat_succ cat_zero) C)) [t : τ (Obj C)] (T : τ (@TerminalObject C t)) (T0 : τ (@TerminalObject (Op_cat
  C) t)) (P : τ (@KernelAdjunctionStructure C S t T)) (Q : τ (@CokernelAdjunctionStructure C S t T0)) (D : τ
  (Functor B (Functor_cat WalkingArrow_cat C))) (E : τ (@OmegaEquivAlong (Functor_cat B C) (@comp_cat_fapp0 B
  (Functor_cat WalkingArrow_cat C) C (@adjunction_coimage_func C S t T T0 P Q) D) (@diagram_family_at_func B
  WalkingArrow_cat C D walking_arrow_tgt) (@fapp0 _ _ (@comp_cat_con_fapp1_func B (Functor_cat WalkingArrow_cat C)
  C D (@adjunction_coimage_func C S t T T0 P Q) (@diagram_evaluation_at_func WalkingArrow_cat C
  walking_arrow_tgt)) (@one_cat_adjunction_coimage_to_target C S C1 t T T0 P Q)))) (V : τ (Functor B C)) (u : τ
  (@Transf B C (@diagram_family_at_func B WalkingArrow_cat C D walking_arrow_src) V)) (z : τ (@= (@Transf B C
  (@comp_cat_fapp0 B (Functor_cat WalkingArrow_cat C) C (@kernel_adjunction_func C S t T P) D) V) (@comp_fapp0
  (Functor_cat B C) (@comp_cat_fapp0 B (Functor_cat WalkingArrow_cat C) C (@kernel_adjunction_func C S t T P) D)
  (@diagram_family_at_func B WalkingArrow_cat C D walking_arrow_src) V u
  (@kernel_adjunction_family_inclusion_transf B C S t T P D)) (@zero_arrow_family_zero_transf B C t T T0
  (@comp_cat_fapp0 B (Functor_cat WalkingArrow_cat C) C (@kernel_adjunction_func C S t T P) D) V)))
 : τ (@= (@Transf B C (@diagram_family_at_func B WalkingArrow_cat C D walking_arrow_src) V) (@comp_fapp0
  (Functor_cat B C) (@diagram_family_at_func B WalkingArrow_cat C D walking_arrow_src) (@diagram_family_at_func B
  WalkingArrow_cat C D walking_arrow_tgt) V (@one_cat_coimage_cover_descent B C S C1 t T T0 P Q D E V u z)
  (@diagram_family_transf B WalkingArrow_cat C D walking_arrow_src walking_arrow_tgt walking_arrow_generator)) u)
≔ @eq_trans _ _ _ _ (@eq_sym _ _ _ (@comp_assoc (Functor_cat B C) (@diagram_family_at_func B WalkingArrow_cat C D
  walking_arrow_src) (@diagram_family_at_func B WalkingArrow_cat C D walking_arrow_tgt) (@comp_cat_fapp0 B
  (Functor_cat WalkingArrow_cat C) C (@adjunction_coimage_func C S t T T0 P Q) D) V
  (@one_cat_coimage_family_descent B C S C1 t T T0 P Q D V u z) (@omega_equiv_along_left_inv (Functor_cat B
  C) (@comp_cat_fapp0 B (Functor_cat WalkingArrow_cat C) C (@adjunction_coimage_func C S t T T0 P Q) D)
  (@diagram_family_at_func B WalkingArrow_cat C D walking_arrow_tgt) (@fapp0 _ _ (@comp_cat_con_fapp1_func B
  (Functor_cat WalkingArrow_cat C) C D (@adjunction_coimage_func C S t T T0 P Q) (@diagram_evaluation_at_func
  WalkingArrow_cat C walking_arrow_tgt)) (@one_cat_adjunction_coimage_to_target C S C1 t T T0 P Q)) E)
  (@diagram_family_transf B WalkingArrow_cat C D walking_arrow_src walking_arrow_tgt walking_arrow_generator)))
  (@eq_trans _ _ _ _ (@eq_ap (@Transf B C (@diagram_family_at_func B WalkingArrow_cat C D walking_arrow_src)
  (@comp_cat_fapp0 B (Functor_cat WalkingArrow_cat C) C (@adjunction_coimage_func C S t T T0 P Q) D)) (@Transf B C
  (@diagram_family_at_func B WalkingArrow_cat C D walking_arrow_src) V) (λ a : τ (@Transf B C
  (@diagram_family_at_func B WalkingArrow_cat C D walking_arrow_src) (@comp_cat_fapp0 B (Functor_cat
  WalkingArrow_cat C) C (@adjunction_coimage_func C S t T T0 P Q) D)), (@comp_fapp0 (Functor_cat B C)
  (@diagram_family_at_func B WalkingArrow_cat C D walking_arrow_src) (@comp_cat_fapp0 B (Functor_cat
  WalkingArrow_cat C) C (@adjunction_coimage_func C S t T T0 P Q) D) V (@one_cat_coimage_family_descent B C
  S C1 t T T0 P Q D V u z) a)) (@comp_fapp0 (Functor_cat B C) (@diagram_family_at_func B WalkingArrow_cat C D
  walking_arrow_src) (@diagram_family_at_func B WalkingArrow_cat C D walking_arrow_tgt) (@comp_cat_fapp0 B
  (Functor_cat WalkingArrow_cat C) C (@adjunction_coimage_func C S t T T0 P Q) D) (@omega_equiv_along_left_inv
  (Functor_cat B C) (@comp_cat_fapp0 B (Functor_cat WalkingArrow_cat C) C (@adjunction_coimage_func C S t T T0 P
  Q) D) (@diagram_family_at_func B WalkingArrow_cat C D walking_arrow_tgt) (@fapp0 _ _ (@comp_cat_con_fapp1_func B
  (Functor_cat WalkingArrow_cat C) C D (@adjunction_coimage_func C S t T T0 P Q) (@diagram_evaluation_at_func
  WalkingArrow_cat C walking_arrow_tgt)) (@one_cat_adjunction_coimage_to_target C S C1 t T T0 P Q)) E)
  (@diagram_family_transf B WalkingArrow_cat C D walking_arrow_src walking_arrow_tgt walking_arrow_generator))
  (@cokernel_adjunction_family_projection_transf B C S t T0 Q (@comp_cat_fapp0 B (Functor_cat WalkingArrow_cat C)
  (Functor_cat WalkingArrow_cat C) (@kernel_adjunction_arrow_func C S t T P) D))
  (@one_cat_coimage_cover_inverse_factor_path B C S C1 t T T0 P Q D E))
  (@one_cat_coimage_family_descent_reconstruction B C S C1 t T T0 P Q D V u z));

// Original quotient cancellation and cover inversion cancel the actual differential.
symbol one_cat_coimage_cover_reflect_path [B C : Cat] [S : τ (@PreadditiveCategory C)] (C1 : τ (IsNCat
  (cat_succ cat_zero) C)) [t : τ (Obj C)] (T : τ (@TerminalObject C t)) (T0 : τ (@TerminalObject (Op_cat C) t)) (P
  : τ (@KernelAdjunctionStructure C S t T)) (Q : τ (@CokernelAdjunctionStructure C S t T0)) (D : τ (Functor B
  (Functor_cat WalkingArrow_cat C))) (E : τ (@OmegaEquivAlong (Functor_cat B C) (@comp_cat_fapp0 B (Functor_cat
  WalkingArrow_cat C) C (@adjunction_coimage_func C S t T T0 P Q) D) (@diagram_family_at_func B WalkingArrow_cat C
  D walking_arrow_tgt) (@fapp0 _ _ (@comp_cat_con_fapp1_func B (Functor_cat WalkingArrow_cat C) C D
  (@adjunction_coimage_func C S t T T0 P Q) (@diagram_evaluation_at_func WalkingArrow_cat C walking_arrow_tgt))
  (@one_cat_adjunction_coimage_to_target C S C1 t T T0 P Q)))) (V : τ (Functor B C)) (u v : τ (@Transf B C
  (@diagram_family_at_func B WalkingArrow_cat C D walking_arrow_tgt) V)) (p : τ (@= (@Transf B C
  (@diagram_family_at_func B WalkingArrow_cat C D walking_arrow_src) V) (@comp_fapp0 (Functor_cat B C)
  (@diagram_family_at_func B WalkingArrow_cat C D walking_arrow_src) (@diagram_family_at_func B WalkingArrow_cat C
  D walking_arrow_tgt) V u (@diagram_family_transf B WalkingArrow_cat C D walking_arrow_src walking_arrow_tgt
  walking_arrow_generator)) (@comp_fapp0 (Functor_cat B C) (@diagram_family_at_func B WalkingArrow_cat C D
  walking_arrow_src) (@diagram_family_at_func B WalkingArrow_cat C D walking_arrow_tgt) V v
  (@diagram_family_transf B WalkingArrow_cat C D walking_arrow_src walking_arrow_tgt walking_arrow_generator))))
 : τ (@= (@Transf B C (@diagram_family_at_func B WalkingArrow_cat C D walking_arrow_tgt) V) u v)
≔ @omega_equiv_precomp_reflect_path (Functor_cat B C) (@comp_cat_fapp0 B (Functor_cat WalkingArrow_cat C) C
  (@adjunction_coimage_func C S t T T0 P Q) D) (@diagram_family_at_func B WalkingArrow_cat C D walking_arrow_tgt)
  (@fapp0 _ _ (@comp_cat_con_fapp1_func B (Functor_cat WalkingArrow_cat C) C D (@adjunction_coimage_func C S t T
  T0 P Q) (@diagram_evaluation_at_func WalkingArrow_cat C walking_arrow_tgt))
  (@one_cat_adjunction_coimage_to_target C S C1 t T T0 P Q)) E V u v
  (@one_cat_cokernel_family_quotient_reflect_path B C S C1 t T T0 Q (@comp_cat_fapp0 B (Functor_cat
  WalkingArrow_cat C) (Functor_cat WalkingArrow_cat C) (@kernel_adjunction_arrow_func C S t T P) D) V (@comp_fapp0
  (Functor_cat B C) (@comp_cat_fapp0 B (Functor_cat WalkingArrow_cat C) C (@adjunction_coimage_func C S t T T0 P
  Q) D) (@diagram_family_at_func B WalkingArrow_cat C D walking_arrow_tgt) V u (@fapp0 _ _
  (@comp_cat_con_fapp1_func B (Functor_cat WalkingArrow_cat C) C D (@adjunction_coimage_func C S t T T0 P Q)
  (@diagram_evaluation_at_func WalkingArrow_cat C walking_arrow_tgt)) (@one_cat_adjunction_coimage_to_target C S
  C1 t T T0 P Q))) (@comp_fapp0 (Functor_cat B C) (@comp_cat_fapp0 B (Functor_cat WalkingArrow_cat C) C
  (@adjunction_coimage_func C S t T T0 P Q) D) (@diagram_family_at_func B WalkingArrow_cat C D walking_arrow_tgt)
  V v (@fapp0 _ _ (@comp_cat_con_fapp1_func B (Functor_cat WalkingArrow_cat C) C D (@adjunction_coimage_func C S t
  T T0 P Q) (@diagram_evaluation_at_func WalkingArrow_cat C walking_arrow_tgt))
  (@one_cat_adjunction_coimage_to_target C S C1 t T T0 P Q))) (@eq_trans _ _ _ _ (@eq_sym _ _ _ (@comp_assoc
  (Functor_cat B C) (@diagram_family_at_func B WalkingArrow_cat C D walking_arrow_src) (@comp_cat_fapp0 B
  (Functor_cat WalkingArrow_cat C) C (@adjunction_coimage_func C S t T T0 P Q) D) (@diagram_family_at_func B
  WalkingArrow_cat C D walking_arrow_tgt) V u (@fapp0 _ _ (@comp_cat_con_fapp1_func B (Functor_cat
  WalkingArrow_cat C) C D (@adjunction_coimage_func C S t T T0 P Q) (@diagram_evaluation_at_func WalkingArrow_cat
  C walking_arrow_tgt)) (@one_cat_adjunction_coimage_to_target C S C1 t T T0 P Q))
  (@cokernel_adjunction_family_projection_transf B C S t T0 Q (@comp_cat_fapp0 B (Functor_cat WalkingArrow_cat C)
  (Functor_cat WalkingArrow_cat C) (@kernel_adjunction_arrow_func C S t T P) D)))) (@eq_trans _ _ _ _ (@eq_ap
  (@Transf B C (@diagram_family_at_func B WalkingArrow_cat C D walking_arrow_src) (@diagram_family_at_func B
  WalkingArrow_cat C D walking_arrow_tgt)) (@Transf B C (@diagram_family_at_func B WalkingArrow_cat C D
  walking_arrow_src) V) (λ b : τ (@Transf B C (@diagram_family_at_func B WalkingArrow_cat C D walking_arrow_src)
  (@diagram_family_at_func B WalkingArrow_cat C D walking_arrow_tgt)), (@comp_fapp0 (Functor_cat B C)
  (@diagram_family_at_func B WalkingArrow_cat C D walking_arrow_src) (@diagram_family_at_func B WalkingArrow_cat C
  D walking_arrow_tgt) V u b)) (@comp_fapp0 (Functor_cat B C) (@diagram_family_at_func B WalkingArrow_cat C D
  walking_arrow_src) (@comp_cat_fapp0 B (Functor_cat WalkingArrow_cat C) C (@adjunction_coimage_func C S t T T0 P
  Q) D) (@diagram_family_at_func B WalkingArrow_cat C D walking_arrow_tgt) (@fapp0 _ _ (@comp_cat_con_fapp1_func B
  (Functor_cat WalkingArrow_cat C) C D (@adjunction_coimage_func C S t T T0 P Q) (@diagram_evaluation_at_func
  WalkingArrow_cat C walking_arrow_tgt)) (@one_cat_adjunction_coimage_to_target C S C1 t T T0 P Q))
  (@cokernel_adjunction_family_projection_transf B C S t T0 Q (@comp_cat_fapp0 B (Functor_cat WalkingArrow_cat C)
  (Functor_cat WalkingArrow_cat C) (@kernel_adjunction_arrow_func C S t T P) D))) (@diagram_family_transf B
  WalkingArrow_cat C D walking_arrow_src walking_arrow_tgt walking_arrow_generator)
  (@one_cat_coimage_family_factor_path B C S C1 t T T0 P Q D)) (@eq_trans _ _ _ _ p (@eq_trans _ _ _ _
  (@eq_ap (@Transf B C (@diagram_family_at_func B WalkingArrow_cat C D walking_arrow_src) (@diagram_family_at_func
  B WalkingArrow_cat C D walking_arrow_tgt)) (@Transf B C (@diagram_family_at_func B WalkingArrow_cat C D
  walking_arrow_src) V) (λ b : τ (@Transf B C (@diagram_family_at_func B WalkingArrow_cat C D walking_arrow_src)
  (@diagram_family_at_func B WalkingArrow_cat C D walking_arrow_tgt)), (@comp_fapp0 (Functor_cat B C)
  (@diagram_family_at_func B WalkingArrow_cat C D walking_arrow_src) (@diagram_family_at_func B WalkingArrow_cat C
  D walking_arrow_tgt) V v b)) (@diagram_family_transf B WalkingArrow_cat C D walking_arrow_src walking_arrow_tgt
  walking_arrow_generator) (@comp_fapp0 (Functor_cat B C) (@diagram_family_at_func B WalkingArrow_cat C D
  walking_arrow_src) (@comp_cat_fapp0 B (Functor_cat WalkingArrow_cat C) C (@adjunction_coimage_func C S t T T0 P
  Q) D) (@diagram_family_at_func B WalkingArrow_cat C D walking_arrow_tgt) (@fapp0 _ _ (@comp_cat_con_fapp1_func B
  (Functor_cat WalkingArrow_cat C) C D (@adjunction_coimage_func C S t T T0 P Q) (@diagram_evaluation_at_func
  WalkingArrow_cat C walking_arrow_tgt)) (@one_cat_adjunction_coimage_to_target C S C1 t T T0 P Q))
  (@cokernel_adjunction_family_projection_transf B C S t T0 Q (@comp_cat_fapp0 B (Functor_cat WalkingArrow_cat C)
  (Functor_cat WalkingArrow_cat C) (@kernel_adjunction_arrow_func C S t T P) D))) (@eq_sym (@Transf B C
  (@diagram_family_at_func B WalkingArrow_cat C D walking_arrow_src) (@diagram_family_at_func B WalkingArrow_cat C
  D walking_arrow_tgt)) (@comp_fapp0 (Functor_cat B C) (@diagram_family_at_func B WalkingArrow_cat C D
  walking_arrow_src) (@comp_cat_fapp0 B (Functor_cat WalkingArrow_cat C) C (@adjunction_coimage_func C S t T T0 P
  Q) D) (@diagram_family_at_func B WalkingArrow_cat C D walking_arrow_tgt) (@fapp0 _ _ (@comp_cat_con_fapp1_func B
  (Functor_cat WalkingArrow_cat C) C D (@adjunction_coimage_func C S t T T0 P Q) (@diagram_evaluation_at_func
  WalkingArrow_cat C walking_arrow_tgt)) (@one_cat_adjunction_coimage_to_target C S C1 t T T0 P Q))
  (@cokernel_adjunction_family_projection_transf B C S t T0 Q (@comp_cat_fapp0 B (Functor_cat WalkingArrow_cat C)
  (Functor_cat WalkingArrow_cat C) (@kernel_adjunction_arrow_func C S t T P) D))) (@diagram_family_transf B
  WalkingArrow_cat C D walking_arrow_src walking_arrow_tgt walking_arrow_generator)
  (@one_cat_coimage_family_factor_path B C S C1 t T T0 P Q D))) (@comp_assoc (Functor_cat B C)
  (@diagram_family_at_func B WalkingArrow_cat C D walking_arrow_src) (@comp_cat_fapp0 B (Functor_cat
  WalkingArrow_cat C) C (@adjunction_coimage_func C S t T T0 P Q) D) (@diagram_family_at_func B WalkingArrow_cat C
  D walking_arrow_tgt) V v (@fapp0 _ _ (@comp_cat_con_fapp1_func B (Functor_cat WalkingArrow_cat C) C D
  (@adjunction_coimage_func C S t T T0 P Q) (@diagram_evaluation_at_func WalkingArrow_cat C walking_arrow_tgt))
  (@one_cat_adjunction_coimage_to_target C S C1 t T T0 P Q)) (@cokernel_adjunction_family_projection_transf B C S
  t T0 Q (@comp_cat_fapp0 B (Functor_cat WalkingArrow_cat C) (Functor_cat WalkingArrow_cat C)
  (@kernel_adjunction_arrow_func C S t T P) D))))))));
