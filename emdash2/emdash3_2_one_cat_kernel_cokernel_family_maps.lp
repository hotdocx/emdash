require open emdash.emdash3_2_functor_category_unit_views;
require open emdash.emdash3_2_one_cat_kernel_family_projection_paths;
require open emdash.emdash3_2_one_cat_cokernel_family_projection_paths;
require open emdash.emdash3_2_one_cat_family_naturality_paths;
require open emdash.emdash3_2_product_family_action_views;
require open emdash.emdash3_2_adjunction_untranspose_naturality;
require open emdash.emdash3_2_one_cat_adjunction_transpose_paths;
require open emdash.emdash3_2_one_cat_adjunction_family_reindex;

// Existing kernel functor action on the original whole diagram map.
symbol kernel_adjunction_family_map_transf [B C : Cat] [S : τ (@PreadditiveCategory C)] (C1 : τ (IsNCat
  (cat_succ cat_zero) C)) [t : τ (Obj C)] (T : τ (@TerminalObject C t)) (T0 : τ (@TerminalObject (Op_cat C) t)) (P
  : τ (@KernelAdjunctionStructure C S t T)) (Q : τ (@CokernelAdjunctionStructure C S t T0)) (D E : τ (Functor B
  (Functor_cat WalkingArrow_cat C))) (m : τ (@Transf B (Functor_cat WalkingArrow_cat C) D E))
 : τ (@Transf B C (@comp_cat_fapp0 B (Functor_cat WalkingArrow_cat C) C (@kernel_adjunction_func C S t T P) D)
  (@comp_cat_fapp0 B (Functor_cat WalkingArrow_cat C) C (@kernel_adjunction_func C S t T P) E))
≔ (@fapp1_fapp0 (Functor_cat B (Functor_cat WalkingArrow_cat C)) (Functor_cat B C) (@comp_cat_cov_func B
  (Functor_cat WalkingArrow_cat C) C (@kernel_adjunction_func C S t T P)) D E m);

// Existing cokernel functor action on the original whole diagram map.
symbol cokernel_adjunction_family_map_transf [B C : Cat] [S : τ (@PreadditiveCategory C)] (C1 : τ (IsNCat
  (cat_succ cat_zero) C)) [t : τ (Obj C)] (T : τ (@TerminalObject C t)) (T0 : τ (@TerminalObject (Op_cat C) t)) (P
  : τ (@KernelAdjunctionStructure C S t T)) (Q : τ (@CokernelAdjunctionStructure C S t T0)) (D E : τ (Functor B
  (Functor_cat WalkingArrow_cat C))) (m : τ (@Transf B (Functor_cat WalkingArrow_cat C) D E))
 : τ (@Transf B C (@comp_cat_fapp0 B (Functor_cat WalkingArrow_cat C) C (@cokernel_adjunction_func C S t T0 Q) D)
  (@comp_cat_fapp0 B (Functor_cat WalkingArrow_cat C) C (@cokernel_adjunction_func C S t T0 Q) E))
≔ (@fapp1_fapp0 (Functor_cat B (Functor_cat WalkingArrow_cat C)) (Functor_cat B C) (@comp_cat_cov_func B
  (Functor_cat WalkingArrow_cat C) C (@cokernel_adjunction_func C S t T0 Q)) D E m);

// The original K action is read through native inverse mating and shape evaluation.
symbol one_cat_kernel_family_map_inclusion_path [B C : Cat] [S : τ (@PreadditiveCategory C)] (C1 : τ (IsNCat
  (cat_succ cat_zero) C)) [t : τ (Obj C)] (T : τ (@TerminalObject C t)) (T0 : τ (@TerminalObject (Op_cat C) t)) (P
  : τ (@KernelAdjunctionStructure C S t T)) (Q : τ (@CokernelAdjunctionStructure C S t T0)) (D E : τ (Functor B
  (Functor_cat WalkingArrow_cat C))) (m : τ (@Transf B (Functor_cat WalkingArrow_cat C) D E))
 : τ (@= (@Transf B C (@comp_cat_fapp0 B (Functor_cat WalkingArrow_cat C) C (@kernel_adjunction_func C S t T P) D)
  (@diagram_family_at_func B WalkingArrow_cat C E walking_arrow_src)) (@comp_fapp0 (Functor_cat B C)
  (@comp_cat_fapp0 B (Functor_cat WalkingArrow_cat C) C (@kernel_adjunction_func C S t T P) D) (@comp_cat_fapp0 B
  (Functor_cat WalkingArrow_cat C) C (@kernel_adjunction_func C S t T P) E) (@diagram_family_at_func B
  WalkingArrow_cat C E walking_arrow_src) (@kernel_adjunction_family_inclusion_transf B C S t T P E)
  (@kernel_adjunction_family_map_transf B C S C1 t T T0 P Q D E m)) (@comp_fapp0 (Functor_cat B C)
  (@comp_cat_fapp0 B (Functor_cat WalkingArrow_cat C) C (@kernel_adjunction_func C S t T P) D)
  (@diagram_family_at_func B WalkingArrow_cat C D walking_arrow_src) (@diagram_family_at_func B WalkingArrow_cat C
  E walking_arrow_src) (@sym_transf_tapp0_transf B WalkingArrow_cat C D E m walking_arrow_src)
  (@kernel_adjunction_family_inclusion_transf B C S t T P D)))
≔ (@eq_trans _ _ _ _ (@eq_sym _ _ _ (@one_cat_kernel_family_projection_path B C S C1 t T P (@comp_cat_fapp0 B
  (Functor_cat WalkingArrow_cat C) C (@kernel_adjunction_func C S t T P) D) E
  (@kernel_adjunction_family_map_transf B C S C1 t T T0 P Q D E m))) (@eq_trans _ _ _ _ (@eq_ap (@Transf B
  (Functor_cat WalkingArrow_cat C) (@comp_cat_fapp0 B C (Functor_cat WalkingArrow_cat C)
  (@terminal_arrow_diagram_func C t T) (@comp_cat_fapp0 B (Functor_cat WalkingArrow_cat C) C
  (@kernel_adjunction_func C S t T P) D)) E) (@Transf B C (@comp_cat_fapp0 B (Functor_cat WalkingArrow_cat C) C
  (@kernel_adjunction_func C S t T P) D) (@diagram_family_at_func B WalkingArrow_cat C E walking_arrow_src)) (λ h
  : τ (@Transf B (Functor_cat WalkingArrow_cat C) (@comp_cat_fapp0 B C (Functor_cat WalkingArrow_cat C)
  (@terminal_arrow_diagram_func C t T) (@comp_cat_fapp0 B (Functor_cat WalkingArrow_cat C) C
  (@kernel_adjunction_func C S t T P) D)) E), (@sym_transf_tapp0_transf B WalkingArrow_cat C (@comp_cat_fapp0 B C
  (Functor_cat WalkingArrow_cat C) (@terminal_arrow_diagram_func C t T) (@comp_cat_fapp0 B (Functor_cat
  WalkingArrow_cat C) C (@kernel_adjunction_func C S t T P) D)) E h walking_arrow_src)) (@fapp0 _ _
  (@adjunction_untranspose_func (Functor_cat B C) (Functor_cat B (Functor_cat WalkingArrow_cat C))
  (@comp_cat_cov_func B C (Functor_cat WalkingArrow_cat C) (@terminal_arrow_diagram_func C t T))
  (@comp_cat_cov_func B (Functor_cat WalkingArrow_cat C) C (@kernel_adjunction_func C S t T P))
  (@one_cat_postcomp_adjunction B C (Functor_cat WalkingArrow_cat C) C1 (@one_cat_functor_category
  WalkingArrow_cat C C1) (@terminal_arrow_diagram_func C t T) (@kernel_adjunction_func C S t T P)
  (@kernel_adjunction_evidence C S t T P)) (@comp_cat_fapp0 B (Functor_cat WalkingArrow_cat C) C
  (@kernel_adjunction_func C S t T P) D) E) (@kernel_adjunction_family_map_transf B C S C1 t T T0 P Q D E
  m)) (@comp_fapp0 (Functor_cat B (Functor_cat WalkingArrow_cat C)) (@comp_cat_fapp0 B C (Functor_cat
  WalkingArrow_cat C) (@terminal_arrow_diagram_func C t T) (@comp_cat_fapp0 B (Functor_cat WalkingArrow_cat C) C
  (@kernel_adjunction_func C S t T P) D)) D E m (@fapp0 _ _ (@adjunction_untranspose_func (Functor_cat B C)
  (Functor_cat B (Functor_cat WalkingArrow_cat C)) (@comp_cat_cov_func B C (Functor_cat WalkingArrow_cat C)
  (@terminal_arrow_diagram_func C t T)) (@comp_cat_cov_func B (Functor_cat WalkingArrow_cat C) C
  (@kernel_adjunction_func C S t T P)) (@one_cat_postcomp_adjunction B C (Functor_cat WalkingArrow_cat C) C1
  (@one_cat_functor_category WalkingArrow_cat C C1) (@terminal_arrow_diagram_func C t T) (@kernel_adjunction_func
  C S t T P) (@kernel_adjunction_evidence C S t T P)) (@comp_cat_fapp0 B (Functor_cat WalkingArrow_cat C) C
  (@kernel_adjunction_func C S t T P) D) D) (@id (Functor_cat B C) (@comp_cat_fapp0 B (Functor_cat
  WalkingArrow_cat C) C (@kernel_adjunction_func C S t T P) D)))) (@eq_trans _ _ _ _ (@eq_sym _ _ _ (@eq_ap
  (@Transf B C (@comp_cat_fapp0 B (Functor_cat WalkingArrow_cat C) C (@kernel_adjunction_func C S t T P) D)
  (@fapp0 (Functor_cat B (Functor_cat WalkingArrow_cat C)) (Functor_cat B C) (@comp_cat_cov_func B (Functor_cat
  WalkingArrow_cat C) C (@kernel_adjunction_func C S t T P)) E)) (@Transf B (Functor_cat WalkingArrow_cat C)
  (@comp_cat_fapp0 B C (Functor_cat WalkingArrow_cat C) (@terminal_arrow_diagram_func C t T) (@comp_cat_fapp0 B
  (Functor_cat WalkingArrow_cat C) C (@kernel_adjunction_func C S t T P) D)) E) (λ v : τ (@Transf B C
  (@comp_cat_fapp0 B (Functor_cat WalkingArrow_cat C) C (@kernel_adjunction_func C S t T P) D) (@fapp0
  (Functor_cat B (Functor_cat WalkingArrow_cat C)) (Functor_cat B C) (@comp_cat_cov_func B (Functor_cat
  WalkingArrow_cat C) C (@kernel_adjunction_func C S t T P)) E)), (@fapp0 _ _ (@adjunction_untranspose_func
  (Functor_cat B C) (Functor_cat B (Functor_cat WalkingArrow_cat C)) (@comp_cat_cov_func B C (Functor_cat
  WalkingArrow_cat C) (@terminal_arrow_diagram_func C t T)) (@comp_cat_cov_func B (Functor_cat WalkingArrow_cat C)
  C (@kernel_adjunction_func C S t T P)) (@one_cat_postcomp_adjunction B C (Functor_cat WalkingArrow_cat C) C1
  (@one_cat_functor_category WalkingArrow_cat C C1) (@terminal_arrow_diagram_func C t T) (@kernel_adjunction_func
  C S t T P) (@kernel_adjunction_evidence C S t T P)) (@comp_cat_fapp0 B (Functor_cat WalkingArrow_cat C) C
  (@kernel_adjunction_func C S t T P) D) E) v)) (@comp_fapp0 (Functor_cat B C) (@comp_cat_fapp0 B (Functor_cat
  WalkingArrow_cat C) C (@kernel_adjunction_func C S t T P) D) (@fapp0 (Functor_cat B (Functor_cat
  WalkingArrow_cat C)) (Functor_cat B C) (@comp_cat_cov_func B (Functor_cat WalkingArrow_cat C) C
  (@kernel_adjunction_func C S t T P)) D) (@fapp0 (Functor_cat B (Functor_cat WalkingArrow_cat C)) (Functor_cat B
  C) (@comp_cat_cov_func B (Functor_cat WalkingArrow_cat C) C (@kernel_adjunction_func C S t T P)) E)
  (@fapp1_fapp0 (Functor_cat B (Functor_cat WalkingArrow_cat C)) (Functor_cat B C) (@comp_cat_cov_func B
  (Functor_cat WalkingArrow_cat C) C (@kernel_adjunction_func C S t T P)) D E m) (@id (Functor_cat B C)
  (@comp_cat_fapp0 B (Functor_cat WalkingArrow_cat C) C (@kernel_adjunction_func C S t T P) D)))
  (@kernel_adjunction_family_map_transf B C S C1 t T T0 P Q D E m) (@eq_refl (@Transf B C (@comp_cat_fapp0 B
  (Functor_cat WalkingArrow_cat C) C (@kernel_adjunction_func C S t T P) D) (@fapp0 (Functor_cat B (Functor_cat
  WalkingArrow_cat C)) (Functor_cat B C) (@comp_cat_cov_func B (Functor_cat WalkingArrow_cat C) C
  (@kernel_adjunction_func C S t T P)) E)) (@kernel_adjunction_family_map_transf B C S C1 t T T0 P Q D E
  m)))) (@eq_sym _ _ _ (@untranspose_postcomp_path (Functor_cat B C) (Functor_cat B (Functor_cat WalkingArrow_cat
  C)) (@comp_cat_cov_func B C (Functor_cat WalkingArrow_cat C) (@terminal_arrow_diagram_func C t T))
  (@comp_cat_cov_func B (Functor_cat WalkingArrow_cat C) C (@kernel_adjunction_func C S t T P))
  (@one_cat_postcomp_adjunction B C (Functor_cat WalkingArrow_cat C) C1 (@one_cat_functor_category
  WalkingArrow_cat C C1) (@terminal_arrow_diagram_func C t T) (@kernel_adjunction_func C S t T P)
  (@kernel_adjunction_evidence C S t T P)) (@comp_cat_fapp0 B (Functor_cat WalkingArrow_cat C) C
  (@kernel_adjunction_func C S t T P) D) D E (@id (Functor_cat B C) (@comp_cat_fapp0 B (Functor_cat
  WalkingArrow_cat C) C (@kernel_adjunction_func C S t T P) D)) m)))) (@eq_trans _ _ _ _
  (@one_cat_diagram_family_evaluation_comp_path B WalkingArrow_cat C C1 walking_arrow_src (@comp_cat_fapp0 B C
  (Functor_cat WalkingArrow_cat C) (@terminal_arrow_diagram_func C t T) (@comp_cat_fapp0 B (Functor_cat
  WalkingArrow_cat C) C (@kernel_adjunction_func C S t T P) D)) D E m (@fapp0 _ _ (@adjunction_untranspose_func
  (Functor_cat B C) (Functor_cat B (Functor_cat WalkingArrow_cat C)) (@comp_cat_cov_func B C (Functor_cat
  WalkingArrow_cat C) (@terminal_arrow_diagram_func C t T)) (@comp_cat_cov_func B (Functor_cat WalkingArrow_cat C)
  C (@kernel_adjunction_func C S t T P)) (@one_cat_postcomp_adjunction B C (Functor_cat WalkingArrow_cat C) C1
  (@one_cat_functor_category WalkingArrow_cat C C1) (@terminal_arrow_diagram_func C t T) (@kernel_adjunction_func
  C S t T P) (@kernel_adjunction_evidence C S t T P)) (@comp_cat_fapp0 B (Functor_cat WalkingArrow_cat C) C
  (@kernel_adjunction_func C S t T P) D) D) (@id (Functor_cat B C) (@comp_cat_fapp0 B (Functor_cat
  WalkingArrow_cat C) C (@kernel_adjunction_func C S t T P) D)))) (@eq_ap (@Transf B C (@comp_cat_fapp0 B
  (Functor_cat WalkingArrow_cat C) C (@kernel_adjunction_func C S t T P) D) (@diagram_family_at_func B
  WalkingArrow_cat C D walking_arrow_src)) (@Transf B C (@comp_cat_fapp0 B (Functor_cat WalkingArrow_cat C) C
  (@kernel_adjunction_func C S t T P) D) (@diagram_family_at_func B WalkingArrow_cat C E walking_arrow_src)) (λ h
  : τ (@Transf B C (@comp_cat_fapp0 B (Functor_cat WalkingArrow_cat C) C (@kernel_adjunction_func C S t T P) D)
  (@diagram_family_at_func B WalkingArrow_cat C D walking_arrow_src)), (@comp_fapp0 (Functor_cat B C)
  (@comp_cat_fapp0 B (Functor_cat WalkingArrow_cat C) C (@kernel_adjunction_func C S t T P) D)
  (@diagram_family_at_func B WalkingArrow_cat C D walking_arrow_src) (@diagram_family_at_func B WalkingArrow_cat C
  E walking_arrow_src) (@sym_transf_tapp0_transf B WalkingArrow_cat C D E m walking_arrow_src) h))
  (@sym_transf_tapp0_transf B WalkingArrow_cat C (@comp_cat_fapp0 B C (Functor_cat WalkingArrow_cat C)
  (@terminal_arrow_diagram_func C t T) (@comp_cat_fapp0 B (Functor_cat WalkingArrow_cat C) C
  (@kernel_adjunction_func C S t T P) D)) D (@fapp0 _ _ (@adjunction_untranspose_func (Functor_cat B C)
  (Functor_cat B (Functor_cat WalkingArrow_cat C)) (@comp_cat_cov_func B C (Functor_cat WalkingArrow_cat C)
  (@terminal_arrow_diagram_func C t T)) (@comp_cat_cov_func B (Functor_cat WalkingArrow_cat C) C
  (@kernel_adjunction_func C S t T P)) (@one_cat_postcomp_adjunction B C (Functor_cat WalkingArrow_cat C) C1
  (@one_cat_functor_category WalkingArrow_cat C C1) (@terminal_arrow_diagram_func C t T) (@kernel_adjunction_func
  C S t T P) (@kernel_adjunction_evidence C S t T P)) (@comp_cat_fapp0 B (Functor_cat WalkingArrow_cat C) C
  (@kernel_adjunction_func C S t T P) D) D) (@id (Functor_cat B C) (@comp_cat_fapp0 B (Functor_cat
  WalkingArrow_cat C) C (@kernel_adjunction_func C S t T P) D))) walking_arrow_src)
  (@kernel_adjunction_family_inclusion_transf B C S t T P D) (@one_cat_kernel_family_projection_path B C S C1 t T
  P (@comp_cat_fapp0 B (Functor_cat WalkingArrow_cat C) C (@kernel_adjunction_func C S t T P) D) D (@id
  (Functor_cat B C) (@comp_cat_fapp0 B (Functor_cat WalkingArrow_cat C) C (@kernel_adjunction_func C S t T P)
  D)))))));

// The original Q action is read through native mating and shape evaluation.
symbol one_cat_cokernel_family_map_projection_path [B C : Cat] [S : τ (@PreadditiveCategory C)] (C1 : τ
  (IsNCat (cat_succ cat_zero) C)) [t : τ (Obj C)] (T : τ (@TerminalObject C t)) (T0 : τ (@TerminalObject (Op_cat
  C) t)) (P : τ (@KernelAdjunctionStructure C S t T)) (Q : τ (@CokernelAdjunctionStructure C S t T0)) (D E : τ
  (Functor B (Functor_cat WalkingArrow_cat C))) (m : τ (@Transf B (Functor_cat WalkingArrow_cat C) D E))
 : τ (@= (@Transf B C (@diagram_family_at_func B WalkingArrow_cat C D walking_arrow_tgt) (@comp_cat_fapp0 B
  (Functor_cat WalkingArrow_cat C) C (@cokernel_adjunction_func C S t T0 Q) E)) (@comp_fapp0 (Functor_cat B C)
  (@diagram_family_at_func B WalkingArrow_cat C D walking_arrow_tgt) (@comp_cat_fapp0 B (Functor_cat
  WalkingArrow_cat C) C (@cokernel_adjunction_func C S t T0 Q) D) (@comp_cat_fapp0 B (Functor_cat WalkingArrow_cat
  C) C (@cokernel_adjunction_func C S t T0 Q) E) (@cokernel_adjunction_family_map_transf B C S C1 t T T0 P Q
  D E m) (@cokernel_adjunction_family_projection_transf B C S t T0 Q D)) (@comp_fapp0 (Functor_cat B C)
  (@diagram_family_at_func B WalkingArrow_cat C D walking_arrow_tgt) (@diagram_family_at_func B WalkingArrow_cat C
  E walking_arrow_tgt) (@comp_cat_fapp0 B (Functor_cat WalkingArrow_cat C) C (@cokernel_adjunction_func C S t T0
  Q) E) (@cokernel_adjunction_family_projection_transf B C S t T0 Q E) (@sym_transf_tapp0_transf B
  WalkingArrow_cat C D E m walking_arrow_tgt)))
≔ (@eq_trans _ _ _ _ (@eq_sym _ _ _ (@one_cat_cokernel_family_projection_path B C S C1 t T0 Q D (@comp_cat_fapp0 B
  (Functor_cat WalkingArrow_cat C) C (@cokernel_adjunction_func C S t T0 Q) E)
  (@cokernel_adjunction_family_map_transf B C S C1 t T T0 P Q D E m))) (@eq_trans _ _ _ _ (@eq_ap (@Transf B
  (Functor_cat WalkingArrow_cat C) D (@comp_cat_fapp0 B C (Functor_cat WalkingArrow_cat C)
  (@initial_arrow_diagram_func C t T0) (@comp_cat_fapp0 B (Functor_cat WalkingArrow_cat C) C
  (@cokernel_adjunction_func C S t T0 Q) E))) (@Transf B C (@diagram_family_at_func B WalkingArrow_cat C D
  walking_arrow_tgt) (@comp_cat_fapp0 B (Functor_cat WalkingArrow_cat C) C (@cokernel_adjunction_func C S t T0 Q)
  E)) (λ h : τ (@Transf B (Functor_cat WalkingArrow_cat C) D (@comp_cat_fapp0 B C (Functor_cat WalkingArrow_cat C)
  (@initial_arrow_diagram_func C t T0) (@comp_cat_fapp0 B (Functor_cat WalkingArrow_cat C) C
  (@cokernel_adjunction_func C S t T0 Q) E))), (@sym_transf_tapp0_transf B WalkingArrow_cat C D (@comp_cat_fapp0 B
  C (Functor_cat WalkingArrow_cat C) (@initial_arrow_diagram_func C t T0) (@comp_cat_fapp0 B (Functor_cat
  WalkingArrow_cat C) C (@cokernel_adjunction_func C S t T0 Q) E)) h walking_arrow_tgt)) (@fapp0 _ _
  (@adjunction_transpose_func (Functor_cat B (Functor_cat WalkingArrow_cat C)) (Functor_cat B C)
  (@comp_cat_cov_func B (Functor_cat WalkingArrow_cat C) C (@cokernel_adjunction_func C S t T0 Q))
  (@comp_cat_cov_func B C (Functor_cat WalkingArrow_cat C) (@initial_arrow_diagram_func C t T0))
  (@one_cat_postcomp_adjunction B (Functor_cat WalkingArrow_cat C) C (@one_cat_functor_category WalkingArrow_cat C
  C1) C1 (@cokernel_adjunction_func C S t T0 Q) (@initial_arrow_diagram_func C t T0)
  (@cokernel_adjunction_evidence C S t T0 Q)) D (@comp_cat_fapp0 B (Functor_cat WalkingArrow_cat C) C
  (@cokernel_adjunction_func C S t T0 Q) E)) (@cokernel_adjunction_family_map_transf B C S C1 t T T0 P Q D E
  m)) (@comp_fapp0 (Functor_cat B (Functor_cat WalkingArrow_cat C)) D E (@comp_cat_fapp0 B C (Functor_cat
  WalkingArrow_cat C) (@initial_arrow_diagram_func C t T0) (@comp_cat_fapp0 B (Functor_cat WalkingArrow_cat C) C
  (@cokernel_adjunction_func C S t T0 Q) E)) (@fapp0 _ _ (@adjunction_transpose_func (Functor_cat B (Functor_cat
  WalkingArrow_cat C)) (Functor_cat B C) (@comp_cat_cov_func B (Functor_cat WalkingArrow_cat C) C
  (@cokernel_adjunction_func C S t T0 Q)) (@comp_cat_cov_func B C (Functor_cat WalkingArrow_cat C)
  (@initial_arrow_diagram_func C t T0)) (@one_cat_postcomp_adjunction B (Functor_cat WalkingArrow_cat C) C
  (@one_cat_functor_category WalkingArrow_cat C C1) C1 (@cokernel_adjunction_func C S t T0 Q)
  (@initial_arrow_diagram_func C t T0) (@cokernel_adjunction_evidence C S t T0 Q)) E (@comp_cat_fapp0 B
  (Functor_cat WalkingArrow_cat C) C (@cokernel_adjunction_func C S t T0 Q) E)) (@id (Functor_cat B C)
  (@comp_cat_fapp0 B (Functor_cat WalkingArrow_cat C) C (@cokernel_adjunction_func C S t T0 Q) E))) m) (@eq_trans
  _ _ _ _ (@eq_sym _ _ _ (@eq_ap (@Transf B C (@fapp0 (Functor_cat B (Functor_cat WalkingArrow_cat C))
  (Functor_cat B C) (@comp_cat_cov_func B (Functor_cat WalkingArrow_cat C) C (@cokernel_adjunction_func C S t T0
  Q)) D) (@comp_cat_fapp0 B (Functor_cat WalkingArrow_cat C) C (@cokernel_adjunction_func C S t T0 Q) E)) (@Transf
  B (Functor_cat WalkingArrow_cat C) D (@comp_cat_fapp0 B C (Functor_cat WalkingArrow_cat C)
  (@initial_arrow_diagram_func C t T0) (@comp_cat_fapp0 B (Functor_cat WalkingArrow_cat C) C
  (@cokernel_adjunction_func C S t T0 Q) E))) (λ v : τ (@Transf B C (@fapp0 (Functor_cat B (Functor_cat
  WalkingArrow_cat C)) (Functor_cat B C) (@comp_cat_cov_func B (Functor_cat WalkingArrow_cat C) C
  (@cokernel_adjunction_func C S t T0 Q)) D) (@comp_cat_fapp0 B (Functor_cat WalkingArrow_cat C) C
  (@cokernel_adjunction_func C S t T0 Q) E)), (@fapp0 _ _ (@adjunction_transpose_func (Functor_cat B (Functor_cat
  WalkingArrow_cat C)) (Functor_cat B C) (@comp_cat_cov_func B (Functor_cat WalkingArrow_cat C) C
  (@cokernel_adjunction_func C S t T0 Q)) (@comp_cat_cov_func B C (Functor_cat WalkingArrow_cat C)
  (@initial_arrow_diagram_func C t T0)) (@one_cat_postcomp_adjunction B (Functor_cat WalkingArrow_cat C) C
  (@one_cat_functor_category WalkingArrow_cat C C1) C1 (@cokernel_adjunction_func C S t T0 Q)
  (@initial_arrow_diagram_func C t T0) (@cokernel_adjunction_evidence C S t T0 Q)) D (@comp_cat_fapp0 B
  (Functor_cat WalkingArrow_cat C) C (@cokernel_adjunction_func C S t T0 Q) E)) v)) (@comp_fapp0 (Functor_cat B C)
  (@fapp0 (Functor_cat B (Functor_cat WalkingArrow_cat C)) (Functor_cat B C) (@comp_cat_cov_func B (Functor_cat
  WalkingArrow_cat C) C (@cokernel_adjunction_func C S t T0 Q)) D) (@fapp0 (Functor_cat B (Functor_cat
  WalkingArrow_cat C)) (Functor_cat B C) (@comp_cat_cov_func B (Functor_cat WalkingArrow_cat C) C
  (@cokernel_adjunction_func C S t T0 Q)) E) (@comp_cat_fapp0 B (Functor_cat WalkingArrow_cat C) C
  (@cokernel_adjunction_func C S t T0 Q) E) (@id (Functor_cat B C) (@comp_cat_fapp0 B (Functor_cat
  WalkingArrow_cat C) C (@cokernel_adjunction_func C S t T0 Q) E)) (@fapp1_fapp0 (Functor_cat B (Functor_cat
  WalkingArrow_cat C)) (Functor_cat B C) (@comp_cat_cov_func B (Functor_cat WalkingArrow_cat C) C
  (@cokernel_adjunction_func C S t T0 Q)) D E m)) (@cokernel_adjunction_family_map_transf B C S C1 t T T0 P
  Q D E m) (@eq_refl (@Transf B C (@fapp0 (Functor_cat B (Functor_cat WalkingArrow_cat C)) (Functor_cat B C)
  (@comp_cat_cov_func B (Functor_cat WalkingArrow_cat C) C (@cokernel_adjunction_func C S t T0 Q)) D)
  (@comp_cat_fapp0 B (Functor_cat WalkingArrow_cat C) C (@cokernel_adjunction_func C S t T0 Q) E))
  (@cokernel_adjunction_family_map_transf B C S C1 t T T0 P Q D E m)))) (@eq_sym _ _ _
  (@one_cat_transpose_precomp_path (Functor_cat B (Functor_cat WalkingArrow_cat C)) (Functor_cat B C)
  (@one_cat_functor_category B (Functor_cat WalkingArrow_cat C) (@one_cat_functor_category WalkingArrow_cat C C1))
  (@one_cat_functor_category B C C1) (@comp_cat_cov_func B (Functor_cat WalkingArrow_cat C) C
  (@cokernel_adjunction_func C S t T0 Q)) (@comp_cat_cov_func B C (Functor_cat WalkingArrow_cat C)
  (@initial_arrow_diagram_func C t T0)) (@one_cat_postcomp_adjunction B (Functor_cat WalkingArrow_cat C) C
  (@one_cat_functor_category WalkingArrow_cat C C1) C1 (@cokernel_adjunction_func C S t T0 Q)
  (@initial_arrow_diagram_func C t T0) (@cokernel_adjunction_evidence C S t T0 Q)) D E (@comp_cat_fapp0 B
  (Functor_cat WalkingArrow_cat C) C (@cokernel_adjunction_func C S t T0 Q) E) m (@id (Functor_cat B C)
  (@comp_cat_fapp0 B (Functor_cat WalkingArrow_cat C) C (@cokernel_adjunction_func C S t T0 Q) E)))))) (@eq_trans
  _ _ _ _ (@one_cat_diagram_family_evaluation_comp_path B WalkingArrow_cat C C1 walking_arrow_tgt D E
  (@comp_cat_fapp0 B C (Functor_cat WalkingArrow_cat C) (@initial_arrow_diagram_func C t T0) (@comp_cat_fapp0 B
  (Functor_cat WalkingArrow_cat C) C (@cokernel_adjunction_func C S t T0 Q) E)) (@fapp0 _ _
  (@adjunction_transpose_func (Functor_cat B (Functor_cat WalkingArrow_cat C)) (Functor_cat B C)
  (@comp_cat_cov_func B (Functor_cat WalkingArrow_cat C) C (@cokernel_adjunction_func C S t T0 Q))
  (@comp_cat_cov_func B C (Functor_cat WalkingArrow_cat C) (@initial_arrow_diagram_func C t T0))
  (@one_cat_postcomp_adjunction B (Functor_cat WalkingArrow_cat C) C (@one_cat_functor_category WalkingArrow_cat C
  C1) C1 (@cokernel_adjunction_func C S t T0 Q) (@initial_arrow_diagram_func C t T0)
  (@cokernel_adjunction_evidence C S t T0 Q)) E (@comp_cat_fapp0 B (Functor_cat WalkingArrow_cat C) C
  (@cokernel_adjunction_func C S t T0 Q) E)) (@id (Functor_cat B C) (@comp_cat_fapp0 B (Functor_cat
  WalkingArrow_cat C) C (@cokernel_adjunction_func C S t T0 Q) E))) m) (@eq_ap (@Transf B C
  (@diagram_family_at_func B WalkingArrow_cat C E walking_arrow_tgt) (@comp_cat_fapp0 B (Functor_cat
  WalkingArrow_cat C) C (@cokernel_adjunction_func C S t T0 Q) E)) (@Transf B C (@diagram_family_at_func B
  WalkingArrow_cat C D walking_arrow_tgt) (@comp_cat_fapp0 B (Functor_cat WalkingArrow_cat C) C
  (@cokernel_adjunction_func C S t T0 Q) E)) (λ h : τ (@Transf B C (@diagram_family_at_func B WalkingArrow_cat C E
  walking_arrow_tgt) (@comp_cat_fapp0 B (Functor_cat WalkingArrow_cat C) C (@cokernel_adjunction_func C S t T0 Q)
  E)), (@comp_fapp0 (Functor_cat B C) (@diagram_family_at_func B WalkingArrow_cat C D walking_arrow_tgt)
  (@diagram_family_at_func B WalkingArrow_cat C E walking_arrow_tgt) (@comp_cat_fapp0 B (Functor_cat
  WalkingArrow_cat C) C (@cokernel_adjunction_func C S t T0 Q) E) h (@sym_transf_tapp0_transf B WalkingArrow_cat C
  D E m walking_arrow_tgt))) (@sym_transf_tapp0_transf B WalkingArrow_cat C E (@comp_cat_fapp0 B C (Functor_cat
  WalkingArrow_cat C) (@initial_arrow_diagram_func C t T0) (@comp_cat_fapp0 B (Functor_cat WalkingArrow_cat C) C
  (@cokernel_adjunction_func C S t T0 Q) E)) (@fapp0 _ _ (@adjunction_transpose_func (Functor_cat B (Functor_cat
  WalkingArrow_cat C)) (Functor_cat B C) (@comp_cat_cov_func B (Functor_cat WalkingArrow_cat C) C
  (@cokernel_adjunction_func C S t T0 Q)) (@comp_cat_cov_func B C (Functor_cat WalkingArrow_cat C)
  (@initial_arrow_diagram_func C t T0)) (@one_cat_postcomp_adjunction B (Functor_cat WalkingArrow_cat C) C
  (@one_cat_functor_category WalkingArrow_cat C C1) C1 (@cokernel_adjunction_func C S t T0 Q)
  (@initial_arrow_diagram_func C t T0) (@cokernel_adjunction_evidence C S t T0 Q)) E (@comp_cat_fapp0 B
  (Functor_cat WalkingArrow_cat C) C (@cokernel_adjunction_func C S t T0 Q) E)) (@id (Functor_cat B C)
  (@comp_cat_fapp0 B (Functor_cat WalkingArrow_cat C) C (@cokernel_adjunction_func C S t T0 Q) E)))
  walking_arrow_tgt) (@cokernel_adjunction_family_projection_transf B C S t T0 Q E)
  (@one_cat_cokernel_family_projection_path B C S C1 t T0 Q E (@comp_cat_fapp0 B (Functor_cat WalkingArrow_cat C)
  C (@cokernel_adjunction_func C S t T0 Q) E) (@id (Functor_cat B C) (@comp_cat_fapp0 B (Functor_cat
  WalkingArrow_cat C) C (@cokernel_adjunction_func C S t T0 Q) E)))))));
