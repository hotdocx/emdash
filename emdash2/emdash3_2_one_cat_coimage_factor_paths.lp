require open emdash.emdash3_2_product_family_action_views;
require open emdash.emdash3_2_one_cat_image_coimage_comparison;
require open emdash.emdash3_2_one_cat_cokernel_family_reconstruction;
require open emdash.emdash3_2_one_cat_kernel_family_reconstruction;
require open emdash.emdash3_2_one_cat_adjunction_zero_column_views;

// The native comparison reconstructs the original whole source-to-image map.
symbol one_cat_coimage_comparison_ambient_path [C : Cat] [S : τ (@PreadditiveCategory C)] (C1 : τ (IsNCat
  (cat_succ cat_zero) C)) [t : τ (Obj C)] (T : τ (@TerminalObject C t)) (T0 : τ (@TerminalObject (Op_cat C) t)) (P
  : τ (@KernelAdjunctionStructure C S t T)) (Q : τ (@CokernelAdjunctionStructure C S t T0)) : τ (@= (@Transf
  (Functor_cat WalkingArrow_cat C) C (@diagram_evaluation_at_func WalkingArrow_cat C walking_arrow_src) (@fapp0 _
  _ (@comp_cat_cov_func (Functor_cat WalkingArrow_cat C) (Functor_cat WalkingArrow_cat C) C
  (@kernel_adjunction_func C S t T P)) (@cokernel_adjunction_arrow_func C S t T0 Q))) (@comp_fapp0 (Functor_cat
  (Functor_cat WalkingArrow_cat C) C) (@diagram_evaluation_at_func WalkingArrow_cat C walking_arrow_src)
  (@adjunction_coimage_func C S t T T0 P Q) (@fapp0 _ _ (@comp_cat_cov_func (Functor_cat WalkingArrow_cat C)
  (Functor_cat WalkingArrow_cat C) C (@kernel_adjunction_func C S t T P)) (@cokernel_adjunction_arrow_func C S t
  T0 Q)) (@one_cat_coimage_image_comparison C S C1 t T T0 P Q) (@cokernel_adjunction_family_projection_transf
  (Functor_cat WalkingArrow_cat C) C S t T0 Q (@kernel_adjunction_arrow_func C S t T P)))
  (@one_cat_adjunction_source_to_image C S C1 t T T0 P Q))
≔ @eq_trans _ _ _ _ (@eq_sym _ _ _ (@one_cat_cokernel_family_projection_path (Functor_cat WalkingArrow_cat C) C S
  C1 t T0 Q (@kernel_adjunction_arrow_func C S t T P) (@fapp0 _ _ (@comp_cat_cov_func (Functor_cat
  WalkingArrow_cat C) (Functor_cat WalkingArrow_cat C) C (@kernel_adjunction_func C S t T P))
  (@cokernel_adjunction_arrow_func C S t T0 Q)) (@one_cat_coimage_image_comparison C S C1 t T T0 P Q)))
  (@one_cat_coimage_image_input_target_path C S C1 t T T0 P Q);

// The original whole kernel observer reconstructs the differential.
symbol one_cat_image_factor_ambient_path [C : Cat] [S : τ (@PreadditiveCategory C)] (C1 : τ (IsNCat
  (cat_succ cat_zero) C)) [t : τ (Obj C)] (T : τ (@TerminalObject C t)) (T0 : τ (@TerminalObject (Op_cat C) t)) (P
  : τ (@KernelAdjunctionStructure C S t T)) (Q : τ (@CokernelAdjunctionStructure C S t T0)) : τ (@= (@Transf
  (Functor_cat WalkingArrow_cat C) C (@diagram_evaluation_at_func WalkingArrow_cat C walking_arrow_src)
  (@diagram_evaluation_at_func WalkingArrow_cat C walking_arrow_tgt)) (@comp_fapp0 (Functor_cat (Functor_cat
  WalkingArrow_cat C) C) (@diagram_evaluation_at_func WalkingArrow_cat C walking_arrow_src) (@fapp0 _ _
  (@comp_cat_cov_func (Functor_cat WalkingArrow_cat C) (Functor_cat WalkingArrow_cat C) C (@kernel_adjunction_func
  C S t T P)) (@cokernel_adjunction_arrow_func C S t T0 Q)) (@diagram_evaluation_at_func WalkingArrow_cat C
  walking_arrow_tgt) (@kernel_adjunction_family_inclusion_transf (Functor_cat WalkingArrow_cat C) C S t T P
  (@cokernel_adjunction_arrow_func C S t T0 Q)) (@one_cat_adjunction_source_to_image C S C1 t T T0 P Q))
  (@diagram_evaluation_transf WalkingArrow_cat C walking_arrow_src walking_arrow_tgt walking_arrow_generator))
≔ @eq_trans _ _ _ _ (@eq_sym _ _ _ (@one_cat_kernel_family_projection_path (Functor_cat WalkingArrow_cat C) C S C1
  t T P (@diagram_evaluation_at_func WalkingArrow_cat C walking_arrow_src) (@cokernel_adjunction_arrow_func C S t
  T0 Q) (@one_cat_adjunction_source_to_image C S C1 t T T0 P Q))) (@one_cat_source_to_image_projection_path C S C1
  t T T0 P Q);

// The original whole cokernel observer reconstructs the differential.
symbol one_cat_coimage_factor_ambient_path [C : Cat] [S : τ (@PreadditiveCategory C)] (C1 : τ (IsNCat
  (cat_succ cat_zero) C)) [t : τ (Obj C)] (T : τ (@TerminalObject C t)) (T0 : τ (@TerminalObject (Op_cat C) t)) (P
  : τ (@KernelAdjunctionStructure C S t T)) (Q : τ (@CokernelAdjunctionStructure C S t T0)) : τ (@= (@Transf
  (Functor_cat WalkingArrow_cat C) C (@diagram_evaluation_at_func WalkingArrow_cat C walking_arrow_src)
  (@diagram_evaluation_at_func WalkingArrow_cat C walking_arrow_tgt)) (@comp_fapp0 (Functor_cat (Functor_cat
  WalkingArrow_cat C) C) (@diagram_evaluation_at_func WalkingArrow_cat C walking_arrow_src)
  (@adjunction_coimage_func C S t T T0 P Q) (@diagram_evaluation_at_func WalkingArrow_cat C walking_arrow_tgt)
  (@one_cat_adjunction_coimage_to_target C S C1 t T T0 P Q) (@cokernel_adjunction_family_projection_transf
  (Functor_cat WalkingArrow_cat C) C S t T0 Q (@kernel_adjunction_arrow_func C S t T P)))
  (@diagram_evaluation_transf WalkingArrow_cat C walking_arrow_src walking_arrow_tgt walking_arrow_generator))
≔ @eq_trans _ _ _ _ (@eq_ap (@Transf (Functor_cat WalkingArrow_cat C) C (@adjunction_coimage_func C S t T T0 P Q)
  (@diagram_evaluation_at_func WalkingArrow_cat C walking_arrow_tgt)) (@Transf (Functor_cat WalkingArrow_cat C) C
  (@diagram_evaluation_at_func WalkingArrow_cat C walking_arrow_src) (@diagram_evaluation_at_func WalkingArrow_cat
  C walking_arrow_tgt)) (λ v : τ (@Transf (Functor_cat WalkingArrow_cat C) C (@adjunction_coimage_func C S t T T0
  P Q) (@diagram_evaluation_at_func WalkingArrow_cat C walking_arrow_tgt)), (@comp_fapp0 (Functor_cat (Functor_cat
  WalkingArrow_cat C) C) (@diagram_evaluation_at_func WalkingArrow_cat C walking_arrow_src)
  (@adjunction_coimage_func C S t T T0 P Q) (@diagram_evaluation_at_func WalkingArrow_cat C walking_arrow_tgt) v
  (@cokernel_adjunction_family_projection_transf (Functor_cat WalkingArrow_cat C) C S t T0 Q
  (@kernel_adjunction_arrow_func C S t T P)))) (@one_cat_adjunction_coimage_to_target C S C1 t T T0 P Q) (@fapp0 _
  _ (@one_cat_adjunction_family_untranspose_func (Functor_cat WalkingArrow_cat C) (Functor_cat WalkingArrow_cat C)
  C (@one_cat_functor_category WalkingArrow_cat C C1) C1 (@cokernel_adjunction_func C S t T0 Q)
  (@initial_arrow_diagram_func C t T0) (@cokernel_adjunction_evidence C S t T0 Q) (@kernel_adjunction_arrow_func C
  S t T P) (@diagram_evaluation_at_func WalkingArrow_cat C walking_arrow_tgt)) (@one_cat_kernel_counit_mate_input
  C S C1 t T T0 P)) (@eq_sym _ _ _ (@one_cat_adjunction_family_untranspose_agrees (Functor_cat WalkingArrow_cat C)
  (Functor_cat WalkingArrow_cat C) C (@one_cat_functor_category WalkingArrow_cat C C1) C1
  (@cokernel_adjunction_func C S t T0 Q) (@initial_arrow_diagram_func C t T0) (@cokernel_adjunction_evidence C S t
  T0 Q) (@kernel_adjunction_arrow_func C S t T P) (@diagram_evaluation_at_func WalkingArrow_cat C
  walking_arrow_tgt) (@one_cat_kernel_counit_mate_input C S C1 t T T0 P)))) (@eq_trans _ _ _ _ (@eq_sym _ _ _
  (@one_cat_cokernel_family_projection_path (Functor_cat WalkingArrow_cat C) C S C1 t T0 Q
  (@kernel_adjunction_arrow_func C S t T P) (@diagram_evaluation_at_func WalkingArrow_cat C walking_arrow_tgt)
  (@fapp0 _ _ (@one_cat_adjunction_family_untranspose_func (Functor_cat WalkingArrow_cat C) (Functor_cat
  WalkingArrow_cat C) C (@one_cat_functor_category WalkingArrow_cat C C1) C1 (@cokernel_adjunction_func C S t T0
  Q) (@initial_arrow_diagram_func C t T0) (@cokernel_adjunction_evidence C S t T0 Q)
  (@kernel_adjunction_arrow_func C S t T P) (@diagram_evaluation_at_func WalkingArrow_cat C walking_arrow_tgt))
  (@one_cat_kernel_counit_mate_input C S C1 t T T0 P)))) (@one_cat_kernel_counit_target_transf_path C S C1 t T T0
  P));

// The canonical coimage factor is determined by its original quotient reconstruction.
symbol one_cat_coimage_target_kernel_factor_path [C : Cat] [S : τ (@PreadditiveCategory C)] (C1 : τ (IsNCat
  (cat_succ cat_zero) C)) [t : τ (Obj C)] (T : τ (@TerminalObject C t)) (T0 : τ (@TerminalObject (Op_cat C) t)) (P
  : τ (@KernelAdjunctionStructure C S t T)) (Q : τ (@CokernelAdjunctionStructure C S t T0)) : τ (@= (@Transf
  (Functor_cat WalkingArrow_cat C) C (@adjunction_coimage_func C S t T T0 P Q) (@diagram_evaluation_at_func
  WalkingArrow_cat C walking_arrow_tgt)) (@comp_fapp0 (Functor_cat (Functor_cat WalkingArrow_cat C) C)
  (@adjunction_coimage_func C S t T T0 P Q) (@fapp0 _ _ (@comp_cat_cov_func (Functor_cat WalkingArrow_cat C)
  (Functor_cat WalkingArrow_cat C) C (@kernel_adjunction_func C S t T P)) (@cokernel_adjunction_arrow_func C S t
  T0 Q)) (@diagram_evaluation_at_func WalkingArrow_cat C walking_arrow_tgt)
  (@kernel_adjunction_family_inclusion_transf (Functor_cat WalkingArrow_cat C) C S t T P
  (@cokernel_adjunction_arrow_func C S t T0 Q)) (@one_cat_coimage_image_comparison C S C1 t T T0 P Q))
  (@one_cat_adjunction_coimage_to_target C S C1 t T T0 P Q))
≔ @one_cat_cokernel_family_quotient_reflect_path (Functor_cat WalkingArrow_cat C) C S C1 t T T0 Q
  (@kernel_adjunction_arrow_func C S t T P) (@diagram_evaluation_at_func WalkingArrow_cat C walking_arrow_tgt)
  (@comp_fapp0 (Functor_cat (Functor_cat WalkingArrow_cat C) C) (@adjunction_coimage_func C S t T T0 P Q) (@fapp0
  _ _ (@comp_cat_cov_func (Functor_cat WalkingArrow_cat C) (Functor_cat WalkingArrow_cat C) C
  (@kernel_adjunction_func C S t T P)) (@cokernel_adjunction_arrow_func C S t T0 Q)) (@diagram_evaluation_at_func
  WalkingArrow_cat C walking_arrow_tgt) (@kernel_adjunction_family_inclusion_transf (Functor_cat WalkingArrow_cat
  C) C S t T P (@cokernel_adjunction_arrow_func C S t T0 Q)) (@one_cat_coimage_image_comparison C S C1 t T T0 P
  Q)) (@one_cat_adjunction_coimage_to_target C S C1 t T T0 P Q) (@eq_trans _ _ _ _ (@eq_sym _ _ _ (@comp_assoc
  (Functor_cat (Functor_cat WalkingArrow_cat C) C) (@diagram_evaluation_at_func WalkingArrow_cat C
  walking_arrow_src) (@adjunction_coimage_func C S t T T0 P Q) (@fapp0 _ _ (@comp_cat_cov_func (Functor_cat
  WalkingArrow_cat C) (Functor_cat WalkingArrow_cat C) C (@kernel_adjunction_func C S t T P))
  (@cokernel_adjunction_arrow_func C S t T0 Q)) (@diagram_evaluation_at_func WalkingArrow_cat C walking_arrow_tgt)
  (@kernel_adjunction_family_inclusion_transf (Functor_cat WalkingArrow_cat C) C S t T P
  (@cokernel_adjunction_arrow_func C S t T0 Q)) (@one_cat_coimage_image_comparison C S C1 t T T0 P Q)
  (@cokernel_adjunction_family_projection_transf (Functor_cat WalkingArrow_cat C) C S t T0 Q
  (@kernel_adjunction_arrow_func C S t T P)))) (@eq_trans _ _ _ _ (@eq_ap (@Transf (Functor_cat WalkingArrow_cat
  C) C (@diagram_evaluation_at_func WalkingArrow_cat C walking_arrow_src) (@fapp0 _ _ (@comp_cat_cov_func
  (Functor_cat WalkingArrow_cat C) (Functor_cat WalkingArrow_cat C) C (@kernel_adjunction_func C S t T P))
  (@cokernel_adjunction_arrow_func C S t T0 Q))) (@Transf (Functor_cat WalkingArrow_cat C) C
  (@diagram_evaluation_at_func WalkingArrow_cat C walking_arrow_src) (@diagram_evaluation_at_func WalkingArrow_cat
  C walking_arrow_tgt)) (λ v : τ (@Transf (Functor_cat WalkingArrow_cat C) C (@diagram_evaluation_at_func
  WalkingArrow_cat C walking_arrow_src) (@fapp0 _ _ (@comp_cat_cov_func (Functor_cat WalkingArrow_cat C)
  (Functor_cat WalkingArrow_cat C) C (@kernel_adjunction_func C S t T P)) (@cokernel_adjunction_arrow_func C S t
  T0 Q))), (@comp_fapp0 (Functor_cat (Functor_cat WalkingArrow_cat C) C) (@diagram_evaluation_at_func
  WalkingArrow_cat C walking_arrow_src) (@fapp0 _ _ (@comp_cat_cov_func (Functor_cat WalkingArrow_cat C)
  (Functor_cat WalkingArrow_cat C) C (@kernel_adjunction_func C S t T P)) (@cokernel_adjunction_arrow_func C S t
  T0 Q)) (@diagram_evaluation_at_func WalkingArrow_cat C walking_arrow_tgt)
  (@kernel_adjunction_family_inclusion_transf (Functor_cat WalkingArrow_cat C) C S t T P
  (@cokernel_adjunction_arrow_func C S t T0 Q)) v)) (@comp_fapp0 (Functor_cat (Functor_cat WalkingArrow_cat C) C)
  (@diagram_evaluation_at_func WalkingArrow_cat C walking_arrow_src) (@adjunction_coimage_func C S t T T0 P Q)
  (@fapp0 _ _ (@comp_cat_cov_func (Functor_cat WalkingArrow_cat C) (Functor_cat WalkingArrow_cat C) C
  (@kernel_adjunction_func C S t T P)) (@cokernel_adjunction_arrow_func C S t T0 Q))
  (@one_cat_coimage_image_comparison C S C1 t T T0 P Q) (@cokernel_adjunction_family_projection_transf
  (Functor_cat WalkingArrow_cat C) C S t T0 Q (@kernel_adjunction_arrow_func C S t T P)))
  (@one_cat_adjunction_source_to_image C S C1 t T T0 P Q) (@one_cat_coimage_comparison_ambient_path C S C1 t
  T T0 P Q)) (@eq_trans _ _ _ _ (@one_cat_image_factor_ambient_path C S C1 t T T0 P Q) (@eq_sym _ _ _
  (@one_cat_coimage_factor_ambient_path C S C1 t T T0 P Q)))));

// The same original image inclusion composed with a equals the original coimage factor.
symbol one_cat_coimage_target_image_factor_path [C : Cat] [S : τ (@PreadditiveCategory C)] (C1 : τ (IsNCat
  (cat_succ cat_zero) C)) [t : τ (Obj C)] (T : τ (@TerminalObject C t)) (T0 : τ (@TerminalObject (Op_cat C) t)) (P
  : τ (@KernelAdjunctionStructure C S t T)) (Q : τ (@CokernelAdjunctionStructure C S t T0)) : τ (@= (@Transf
  (Functor_cat WalkingArrow_cat C) C (@adjunction_coimage_func C S t T T0 P Q) (@diagram_evaluation_at_func
  WalkingArrow_cat C walking_arrow_tgt)) (@comp_fapp0 (Functor_cat (Functor_cat WalkingArrow_cat C) C)
  (@adjunction_coimage_func C S t T T0 P Q) (@fapp0 _ _ (@comp_cat_cov_func (Functor_cat WalkingArrow_cat C)
  (Functor_cat WalkingArrow_cat C) C (@kernel_adjunction_func C S t T P)) (@cokernel_adjunction_arrow_func C S t
  T0 Q)) (@diagram_evaluation_at_func WalkingArrow_cat C walking_arrow_tgt) (@adjunction_image_inclusion C S t T
  T0 P Q) (@one_cat_coimage_image_comparison C S C1 t T T0 P Q)) (@one_cat_adjunction_coimage_to_target C S C1 t T
  T0 P Q))
≔ @eq_trans _ _ _ _ (@eq_ap (@Transf (Functor_cat WalkingArrow_cat C) C (@fapp0 _ _ (@comp_cat_cov_func
  (Functor_cat WalkingArrow_cat C) (Functor_cat WalkingArrow_cat C) C (@kernel_adjunction_func C S t T P))
  (@cokernel_adjunction_arrow_func C S t T0 Q)) (@diagram_evaluation_at_func WalkingArrow_cat C
  walking_arrow_tgt)) (@Transf (Functor_cat WalkingArrow_cat C) C (@adjunction_coimage_func C S t T T0 P Q)
  (@diagram_evaluation_at_func WalkingArrow_cat C walking_arrow_tgt)) (λ v : τ (@Transf (Functor_cat
  WalkingArrow_cat C) C (@fapp0 _ _ (@comp_cat_cov_func (Functor_cat WalkingArrow_cat C) (Functor_cat
  WalkingArrow_cat C) C (@kernel_adjunction_func C S t T P)) (@cokernel_adjunction_arrow_func C S t T0 Q))
  (@diagram_evaluation_at_func WalkingArrow_cat C walking_arrow_tgt)), (@comp_fapp0 (Functor_cat (Functor_cat
  WalkingArrow_cat C) C) (@adjunction_coimage_func C S t T T0 P Q) (@fapp0 _ _ (@comp_cat_cov_func (Functor_cat
  WalkingArrow_cat C) (Functor_cat WalkingArrow_cat C) C (@kernel_adjunction_func C S t T P))
  (@cokernel_adjunction_arrow_func C S t T0 Q)) (@diagram_evaluation_at_func WalkingArrow_cat C walking_arrow_tgt)
  v (@one_cat_coimage_image_comparison C S C1 t T T0 P Q))) (@adjunction_image_inclusion C S t T T0 P Q)
  (@kernel_adjunction_family_inclusion_transf (Functor_cat WalkingArrow_cat C) C S t T P
  (@cokernel_adjunction_arrow_func C S t T0 Q)) (@eq_sym _ _ _ (@one_cat_kernel_family_inclusion_whisker_path
  (Functor_cat WalkingArrow_cat C) C S C1 t T P (@cokernel_adjunction_arrow_func C S t T0 Q))))
  (@one_cat_coimage_target_kernel_factor_path C S C1 t T T0 P Q);
