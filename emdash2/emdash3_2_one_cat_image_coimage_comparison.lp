/* Canonical whole Coim⇒Im from the original K/Q adjunctions.
   Faithful inverse mating derives the whole annihilation u∘κ=0. An existing
   native square in the functor category realizes that single derived cell;
   exchanging and cokernel mating constructs the comparison. Its whole
   factorization and uniqueness are derived, with no opaque comparison or
   caller naturality/cone data. Abelian invertibility is a later obligation. */
require open emdash.emdash3_2_one_cat_kernel_cokernel_family_paths;
require open emdash.emdash3_2_one_cat_adjunction_family_views;
require open emdash.emdash3_2_one_cat_adjunction_zero_column_views;
require open emdash.emdash3_2_one_cat_image_coimage_factors;
require open emdash.emdash3_2_one_cat_arrow_diagrams;
require open emdash.emdash3_2_one_cat_cokernel_family_inputs;

// The original whole u:ev₀⇒Im reconstructs ∂ under projected inverse mating.
symbol one_cat_source_to_image_projection_path [C : Cat] [S : τ (@PreadditiveCategory C)]
  (C1 : τ (IsNCat (cat_succ cat_zero) C)) [t : τ (Obj C)]
  (T : τ (@TerminalObject C t)) (T0 : τ (@TerminalObject (Op_cat C) t))
  (P : τ (@KernelAdjunctionStructure C S t T)) (Q : τ (@CokernelAdjunctionStructure C S t T0))
  : τ (@= (@Transf (Functor_cat WalkingArrow_cat C) C (@diagram_evaluation_at_func WalkingArrow_cat C
    walking_arrow_src) (@diagram_evaluation_at_func WalkingArrow_cat C walking_arrow_tgt)) (@sym_transf_tapp0_transf
    (Functor_cat WalkingArrow_cat C) WalkingArrow_cat C (@fapp0 (Functor_cat (Functor_cat WalkingArrow_cat C) C)
    (Functor_cat (Functor_cat WalkingArrow_cat C) (Functor_cat WalkingArrow_cat C)) (@comp_cat_cov_func (Functor_cat
    WalkingArrow_cat C) C (Functor_cat WalkingArrow_cat C) (@terminal_arrow_diagram_func C t T))
    (@diagram_evaluation_at_func WalkingArrow_cat C walking_arrow_src)) (@cokernel_adjunction_arrow_func C S t T0 Q)
    (@fapp0 _ _ (@adjunction_untranspose_func (Functor_cat (Functor_cat WalkingArrow_cat C) C) (Functor_cat
    (Functor_cat WalkingArrow_cat C) (Functor_cat WalkingArrow_cat C)) (@comp_cat_cov_func (Functor_cat
    WalkingArrow_cat C) C (Functor_cat WalkingArrow_cat C) (@terminal_arrow_diagram_func C t T)) (@comp_cat_cov_func
    (Functor_cat WalkingArrow_cat C) (Functor_cat WalkingArrow_cat C) C (@kernel_adjunction_func C S t T P))
    (@one_cat_postcomp_adjunction (Functor_cat WalkingArrow_cat C) C (Functor_cat WalkingArrow_cat C) C1
    (@one_cat_functor_category WalkingArrow_cat C C1) (@terminal_arrow_diagram_func C t T) (@kernel_adjunction_func C
    S t T P) (@kernel_adjunction_evidence C S t T P)) (@diagram_evaluation_at_func WalkingArrow_cat C
    walking_arrow_src) (@cokernel_adjunction_arrow_func C S t T0 Q)) (@one_cat_adjunction_source_to_image C S C1 t T
    T0 P Q)) walking_arrow_src) (@diagram_evaluation_transf WalkingArrow_cat C walking_arrow_src walking_arrow_tgt
    walking_arrow_generator))
≔ @eq_trans (@Transf (Functor_cat WalkingArrow_cat C) C (@diagram_evaluation_at_func WalkingArrow_cat C
  walking_arrow_src) (@diagram_evaluation_at_func WalkingArrow_cat C walking_arrow_tgt)) (@sym_transf_tapp0_transf
  (Functor_cat WalkingArrow_cat C) WalkingArrow_cat C (@fapp0 (Functor_cat (Functor_cat WalkingArrow_cat C) C)
  (Functor_cat (Functor_cat WalkingArrow_cat C) (Functor_cat WalkingArrow_cat C)) (@comp_cat_cov_func (Functor_cat
  WalkingArrow_cat C) C (Functor_cat WalkingArrow_cat C) (@terminal_arrow_diagram_func C t T))
  (@diagram_evaluation_at_func WalkingArrow_cat C walking_arrow_src)) (@cokernel_adjunction_arrow_func C S t T0 Q)
  (@fapp0 _ _ (@adjunction_untranspose_func (Functor_cat (Functor_cat WalkingArrow_cat C) C) (Functor_cat (Functor_cat
  WalkingArrow_cat C) (Functor_cat WalkingArrow_cat C)) (@comp_cat_cov_func (Functor_cat WalkingArrow_cat C) C
  (Functor_cat WalkingArrow_cat C) (@terminal_arrow_diagram_func C t T)) (@comp_cat_cov_func (Functor_cat
  WalkingArrow_cat C) (Functor_cat WalkingArrow_cat C) C (@kernel_adjunction_func C S t T P))
  (@one_cat_postcomp_adjunction (Functor_cat WalkingArrow_cat C) C (Functor_cat WalkingArrow_cat C) C1
  (@one_cat_functor_category WalkingArrow_cat C C1) (@terminal_arrow_diagram_func C t T) (@kernel_adjunction_func C S
  t T P) (@kernel_adjunction_evidence C S t T P)) (@diagram_evaluation_at_func WalkingArrow_cat C walking_arrow_src)
  (@cokernel_adjunction_arrow_func C S t T0 Q)) (@one_cat_adjunction_source_to_image C S C1 t T T0 P Q))
  walking_arrow_src) (@sym_transf_tapp0_transf (Functor_cat WalkingArrow_cat C) WalkingArrow_cat C (@fapp0
  (Functor_cat (Functor_cat WalkingArrow_cat C) C) (Functor_cat (Functor_cat WalkingArrow_cat C) (Functor_cat
  WalkingArrow_cat C)) (@comp_cat_cov_func (Functor_cat WalkingArrow_cat C) C (Functor_cat WalkingArrow_cat C)
  (@terminal_arrow_diagram_func C t T)) (@diagram_evaluation_at_func WalkingArrow_cat C walking_arrow_src))
  (@cokernel_adjunction_arrow_func C S t T0 Q) (@one_cat_cokernel_unit_mate_input C S C1 t T T0 Q) walking_arrow_src)
  (@diagram_evaluation_transf WalkingArrow_cat C walking_arrow_src walking_arrow_tgt walking_arrow_generator) (@eq_ap
  (@Transf (Functor_cat WalkingArrow_cat C) (Functor_cat WalkingArrow_cat C) (@fapp0 (Functor_cat (Functor_cat
  WalkingArrow_cat C) C) (Functor_cat (Functor_cat WalkingArrow_cat C) (Functor_cat WalkingArrow_cat C))
  (@comp_cat_cov_func (Functor_cat WalkingArrow_cat C) C (Functor_cat WalkingArrow_cat C)
  (@terminal_arrow_diagram_func C t T)) (@diagram_evaluation_at_func WalkingArrow_cat C walking_arrow_src))
  (@cokernel_adjunction_arrow_func C S t T0 Q)) (@Transf (Functor_cat WalkingArrow_cat C) C
  (@diagram_evaluation_at_func WalkingArrow_cat C walking_arrow_src) (@diagram_evaluation_at_func WalkingArrow_cat C
  walking_arrow_tgt)) (λ z : τ (@Transf (Functor_cat WalkingArrow_cat C) (Functor_cat WalkingArrow_cat C) (@fapp0
  (Functor_cat (Functor_cat WalkingArrow_cat C) C) (Functor_cat (Functor_cat WalkingArrow_cat C) (Functor_cat
  WalkingArrow_cat C)) (@comp_cat_cov_func (Functor_cat WalkingArrow_cat C) C (Functor_cat WalkingArrow_cat C)
  (@terminal_arrow_diagram_func C t T)) (@diagram_evaluation_at_func WalkingArrow_cat C walking_arrow_src))
  (@cokernel_adjunction_arrow_func C S t T0 Q)), (@sym_transf_tapp0_transf (Functor_cat WalkingArrow_cat C)
  WalkingArrow_cat C (@fapp0 (Functor_cat (Functor_cat WalkingArrow_cat C) C) (Functor_cat (Functor_cat
  WalkingArrow_cat C) (Functor_cat WalkingArrow_cat C)) (@comp_cat_cov_func (Functor_cat WalkingArrow_cat C) C
  (Functor_cat WalkingArrow_cat C) (@terminal_arrow_diagram_func C t T)) (@diagram_evaluation_at_func WalkingArrow_cat
  C walking_arrow_src)) (@cokernel_adjunction_arrow_func C S t T0 Q) z walking_arrow_src)) (@fapp0 _ _
  (@adjunction_untranspose_func (Functor_cat (Functor_cat WalkingArrow_cat C) C) (Functor_cat (Functor_cat
  WalkingArrow_cat C) (Functor_cat WalkingArrow_cat C)) (@comp_cat_cov_func (Functor_cat WalkingArrow_cat C) C
  (Functor_cat WalkingArrow_cat C) (@terminal_arrow_diagram_func C t T)) (@comp_cat_cov_func (Functor_cat
  WalkingArrow_cat C) (Functor_cat WalkingArrow_cat C) C (@kernel_adjunction_func C S t T P))
  (@one_cat_postcomp_adjunction (Functor_cat WalkingArrow_cat C) C (Functor_cat WalkingArrow_cat C) C1
  (@one_cat_functor_category WalkingArrow_cat C C1) (@terminal_arrow_diagram_func C t T) (@kernel_adjunction_func C S
  t T P) (@kernel_adjunction_evidence C S t T P)) (@diagram_evaluation_at_func WalkingArrow_cat C walking_arrow_src)
  (@cokernel_adjunction_arrow_func C S t T0 Q)) (@one_cat_adjunction_source_to_image C S C1 t T T0 P Q))
  (@one_cat_cokernel_unit_mate_input C S C1 t T T0 Q) (@one_cat_adjunction_family_transpose_reconstruction
  (Functor_cat WalkingArrow_cat C) C (Functor_cat WalkingArrow_cat C) C1 (@one_cat_functor_category WalkingArrow_cat C
  C1) (@terminal_arrow_diagram_func C t T) (@kernel_adjunction_func C S t T P) (@kernel_adjunction_evidence C S t T P)
  (@diagram_evaluation_at_func WalkingArrow_cat C walking_arrow_src) (@cokernel_adjunction_arrow_func C S t T0 Q)
  (@one_cat_cokernel_unit_mate_input C S C1 t T T0 Q))) (@one_cat_cokernel_unit_source_transf_path C S C1 t T T0 Q);

// Whole faithfulness and the original counit derive u∘κ=0 internally.
symbol one_cat_source_to_image_kills_kernel_path [C : Cat] [S : τ (@PreadditiveCategory C)]
  (C1 : τ (IsNCat (cat_succ cat_zero) C)) [t : τ (Obj C)]
  (T : τ (@TerminalObject C t)) (T0 : τ (@TerminalObject (Op_cat C) t))
  (P : τ (@KernelAdjunctionStructure C S t T)) (Q : τ (@CokernelAdjunctionStructure C S t T0))
  : τ (@= (@Transf (Functor_cat WalkingArrow_cat C) C (@kernel_adjunction_func C S t T P) (@fapp0 (Functor_cat
    (Functor_cat WalkingArrow_cat C) (Functor_cat WalkingArrow_cat C)) (Functor_cat (Functor_cat WalkingArrow_cat C)
    C) (@comp_cat_cov_func (Functor_cat WalkingArrow_cat C) (Functor_cat WalkingArrow_cat C) C
    (@kernel_adjunction_func C S t T P)) (@cokernel_adjunction_arrow_func C S t T0 Q))) (@comp_fapp0 (Functor_cat
    (Functor_cat WalkingArrow_cat C) C) (@kernel_adjunction_func C S t T P) (@diagram_evaluation_at_func
    WalkingArrow_cat C walking_arrow_src) (@fapp0 (Functor_cat (Functor_cat WalkingArrow_cat C) (Functor_cat
    WalkingArrow_cat C)) (Functor_cat (Functor_cat WalkingArrow_cat C) C) (@comp_cat_cov_func (Functor_cat
    WalkingArrow_cat C) (Functor_cat WalkingArrow_cat C) C (@kernel_adjunction_func C S t T P))
    (@cokernel_adjunction_arrow_func C S t T0 Q)) (@one_cat_adjunction_source_to_image C S C1 t T T0 P Q)
    (@kernel_adjunction_inclusion C S t T P)) (@comp_fapp0 (Functor_cat (Functor_cat WalkingArrow_cat C) C)
    (@kernel_adjunction_func C S t T P) (@Const_func (Functor_cat WalkingArrow_cat C) C t) (@fapp0 (Functor_cat
    (Functor_cat WalkingArrow_cat C) (Functor_cat WalkingArrow_cat C)) (Functor_cat (Functor_cat WalkingArrow_cat C)
    C) (@comp_cat_cov_func (Functor_cat WalkingArrow_cat C) (Functor_cat WalkingArrow_cat C) C
    (@kernel_adjunction_func C S t T P)) (@cokernel_adjunction_arrow_func C S t T0 Q)) (@diagram_family_transf
    (Functor_cat WalkingArrow_cat C) WalkingArrow_cat C (@comp_cat_fapp0 (Functor_cat WalkingArrow_cat C) C
    (Functor_cat WalkingArrow_cat C) (@initial_arrow_diagram_func C t T0) (@fapp0 (Functor_cat (Functor_cat
    WalkingArrow_cat C) (Functor_cat WalkingArrow_cat C)) (Functor_cat (Functor_cat WalkingArrow_cat C) C)
    (@comp_cat_cov_func (Functor_cat WalkingArrow_cat C) (Functor_cat WalkingArrow_cat C) C (@kernel_adjunction_func C
    S t T P)) (@cokernel_adjunction_arrow_func C S t T0 Q))) walking_arrow_src walking_arrow_tgt
    walking_arrow_generator) (@diagram_family_transf (Functor_cat WalkingArrow_cat C) WalkingArrow_cat C
    (@comp_cat_fapp0 (Functor_cat WalkingArrow_cat C) C (Functor_cat WalkingArrow_cat C) (@terminal_arrow_diagram_func
    C t T) (@kernel_adjunction_func C S t T P)) walking_arrow_src walking_arrow_tgt walking_arrow_generator)))
≔ @one_cat_kernel_family_projection_reflect_path (Functor_cat WalkingArrow_cat C) C S C1 t T T0 P
  (@kernel_adjunction_func C S t T P) (@cokernel_adjunction_arrow_func C S t T0 Q) (@comp_fapp0 (Functor_cat
  (Functor_cat WalkingArrow_cat C) C) (@kernel_adjunction_func C S t T P) (@diagram_evaluation_at_func
  WalkingArrow_cat C walking_arrow_src) (@fapp0 (Functor_cat (Functor_cat WalkingArrow_cat C) (Functor_cat
  WalkingArrow_cat C)) (Functor_cat (Functor_cat WalkingArrow_cat C) C) (@comp_cat_cov_func (Functor_cat
  WalkingArrow_cat C) (Functor_cat WalkingArrow_cat C) C (@kernel_adjunction_func C S t T P))
  (@cokernel_adjunction_arrow_func C S t T0 Q)) (@one_cat_adjunction_source_to_image C S C1 t T T0 P Q)
  (@kernel_adjunction_inclusion C S t T P)) (@comp_fapp0 (Functor_cat (Functor_cat WalkingArrow_cat C) C)
  (@kernel_adjunction_func C S t T P) (@Const_func (Functor_cat WalkingArrow_cat C) C t) (@fapp0 (Functor_cat
  (Functor_cat WalkingArrow_cat C) (Functor_cat WalkingArrow_cat C)) (Functor_cat (Functor_cat WalkingArrow_cat C) C)
  (@comp_cat_cov_func (Functor_cat WalkingArrow_cat C) (Functor_cat WalkingArrow_cat C) C (@kernel_adjunction_func C S
  t T P)) (@cokernel_adjunction_arrow_func C S t T0 Q)) (@diagram_family_transf (Functor_cat WalkingArrow_cat C)
  WalkingArrow_cat C (@comp_cat_fapp0 (Functor_cat WalkingArrow_cat C) C (Functor_cat WalkingArrow_cat C)
  (@initial_arrow_diagram_func C t T0) (@fapp0 (Functor_cat (Functor_cat WalkingArrow_cat C) (Functor_cat
  WalkingArrow_cat C)) (Functor_cat (Functor_cat WalkingArrow_cat C) C) (@comp_cat_cov_func (Functor_cat
  WalkingArrow_cat C) (Functor_cat WalkingArrow_cat C) C (@kernel_adjunction_func C S t T P))
  (@cokernel_adjunction_arrow_func C S t T0 Q))) walking_arrow_src walking_arrow_tgt walking_arrow_generator)
  (@diagram_family_transf (Functor_cat WalkingArrow_cat C) WalkingArrow_cat C (@comp_cat_fapp0 (Functor_cat
  WalkingArrow_cat C) C (Functor_cat WalkingArrow_cat C) (@terminal_arrow_diagram_func C t T) (@kernel_adjunction_func
  C S t T P)) walking_arrow_src walking_arrow_tgt walking_arrow_generator)) (@eq_trans (@Transf (Functor_cat
  WalkingArrow_cat C) C (@kernel_adjunction_func C S t T P) (@diagram_evaluation_at_func WalkingArrow_cat C
  walking_arrow_tgt)) (@sym_transf_tapp0_transf (Functor_cat WalkingArrow_cat C) WalkingArrow_cat C (@fapp0
  (Functor_cat (Functor_cat WalkingArrow_cat C) C) (Functor_cat (Functor_cat WalkingArrow_cat C) (Functor_cat
  WalkingArrow_cat C)) (@comp_cat_cov_func (Functor_cat WalkingArrow_cat C) C (Functor_cat WalkingArrow_cat C)
  (@terminal_arrow_diagram_func C t T)) (@kernel_adjunction_func C S t T P)) (@cokernel_adjunction_arrow_func C S t T0
  Q) (@fapp0 _ _ (@adjunction_untranspose_func (Functor_cat (Functor_cat WalkingArrow_cat C) C) (Functor_cat
  (Functor_cat WalkingArrow_cat C) (Functor_cat WalkingArrow_cat C)) (@comp_cat_cov_func (Functor_cat WalkingArrow_cat
  C) C (Functor_cat WalkingArrow_cat C) (@terminal_arrow_diagram_func C t T)) (@comp_cat_cov_func (Functor_cat
  WalkingArrow_cat C) (Functor_cat WalkingArrow_cat C) C (@kernel_adjunction_func C S t T P))
  (@one_cat_postcomp_adjunction (Functor_cat WalkingArrow_cat C) C (Functor_cat WalkingArrow_cat C) C1
  (@one_cat_functor_category WalkingArrow_cat C C1) (@terminal_arrow_diagram_func C t T) (@kernel_adjunction_func C S
  t T P) (@kernel_adjunction_evidence C S t T P)) (@kernel_adjunction_func C S t T P) (@cokernel_adjunction_arrow_func
  C S t T0 Q)) (@comp_fapp0 (Functor_cat (Functor_cat WalkingArrow_cat C) C) (@kernel_adjunction_func C S t T P)
  (@diagram_evaluation_at_func WalkingArrow_cat C walking_arrow_src) (@fapp0 (Functor_cat (Functor_cat
  WalkingArrow_cat C) (Functor_cat WalkingArrow_cat C)) (Functor_cat (Functor_cat WalkingArrow_cat C) C)
  (@comp_cat_cov_func (Functor_cat WalkingArrow_cat C) (Functor_cat WalkingArrow_cat C) C (@kernel_adjunction_func C S
  t T P)) (@cokernel_adjunction_arrow_func C S t T0 Q)) (@one_cat_adjunction_source_to_image C S C1 t T T0 P Q)
  (@kernel_adjunction_inclusion C S t T P))) walking_arrow_src) (@comp_fapp0 (Functor_cat (Functor_cat
  WalkingArrow_cat C) C) (@kernel_adjunction_func C S t T P) (@diagram_evaluation_at_func WalkingArrow_cat C
  walking_arrow_src) (@diagram_evaluation_at_func WalkingArrow_cat C walking_arrow_tgt) (@sym_transf_tapp0_transf
  (Functor_cat WalkingArrow_cat C) WalkingArrow_cat C (@fapp0 (Functor_cat (Functor_cat WalkingArrow_cat C) C)
  (Functor_cat (Functor_cat WalkingArrow_cat C) (Functor_cat WalkingArrow_cat C)) (@comp_cat_cov_func (Functor_cat
  WalkingArrow_cat C) C (Functor_cat WalkingArrow_cat C) (@terminal_arrow_diagram_func C t T))
  (@diagram_evaluation_at_func WalkingArrow_cat C walking_arrow_src)) (@cokernel_adjunction_arrow_func C S t T0 Q)
  (@fapp0 _ _ (@adjunction_untranspose_func (Functor_cat (Functor_cat WalkingArrow_cat C) C) (Functor_cat (Functor_cat
  WalkingArrow_cat C) (Functor_cat WalkingArrow_cat C)) (@comp_cat_cov_func (Functor_cat WalkingArrow_cat C) C
  (Functor_cat WalkingArrow_cat C) (@terminal_arrow_diagram_func C t T)) (@comp_cat_cov_func (Functor_cat
  WalkingArrow_cat C) (Functor_cat WalkingArrow_cat C) C (@kernel_adjunction_func C S t T P))
  (@one_cat_postcomp_adjunction (Functor_cat WalkingArrow_cat C) C (Functor_cat WalkingArrow_cat C) C1
  (@one_cat_functor_category WalkingArrow_cat C C1) (@terminal_arrow_diagram_func C t T) (@kernel_adjunction_func C S
  t T P) (@kernel_adjunction_evidence C S t T P)) (@diagram_evaluation_at_func WalkingArrow_cat C walking_arrow_src)
  (@cokernel_adjunction_arrow_func C S t T0 Q)) (@one_cat_adjunction_source_to_image C S C1 t T T0 P Q))
  walking_arrow_src) (@kernel_adjunction_inclusion C S t T P)) (@sym_transf_tapp0_transf (Functor_cat WalkingArrow_cat
  C) WalkingArrow_cat C (@fapp0 (Functor_cat (Functor_cat WalkingArrow_cat C) C) (Functor_cat (Functor_cat
  WalkingArrow_cat C) (Functor_cat WalkingArrow_cat C)) (@comp_cat_cov_func (Functor_cat WalkingArrow_cat C) C
  (Functor_cat WalkingArrow_cat C) (@terminal_arrow_diagram_func C t T)) (@kernel_adjunction_func C S t T P))
  (@cokernel_adjunction_arrow_func C S t T0 Q) (@fapp0 _ _ (@adjunction_untranspose_func (Functor_cat (Functor_cat
  WalkingArrow_cat C) C) (Functor_cat (Functor_cat WalkingArrow_cat C) (Functor_cat WalkingArrow_cat C))
  (@comp_cat_cov_func (Functor_cat WalkingArrow_cat C) C (Functor_cat WalkingArrow_cat C)
  (@terminal_arrow_diagram_func C t T)) (@comp_cat_cov_func (Functor_cat WalkingArrow_cat C) (Functor_cat
  WalkingArrow_cat C) C (@kernel_adjunction_func C S t T P)) (@one_cat_postcomp_adjunction (Functor_cat
  WalkingArrow_cat C) C (Functor_cat WalkingArrow_cat C) C1 (@one_cat_functor_category WalkingArrow_cat C C1)
  (@terminal_arrow_diagram_func C t T) (@kernel_adjunction_func C S t T P) (@kernel_adjunction_evidence C S t T P))
  (@kernel_adjunction_func C S t T P) (@cokernel_adjunction_arrow_func C S t T0 Q)) (@comp_fapp0 (Functor_cat
  (Functor_cat WalkingArrow_cat C) C) (@kernel_adjunction_func C S t T P) (@Const_func (Functor_cat WalkingArrow_cat
  C) C t) (@fapp0 (Functor_cat (Functor_cat WalkingArrow_cat C) (Functor_cat WalkingArrow_cat C)) (Functor_cat
  (Functor_cat WalkingArrow_cat C) C) (@comp_cat_cov_func (Functor_cat WalkingArrow_cat C) (Functor_cat
  WalkingArrow_cat C) C (@kernel_adjunction_func C S t T P)) (@cokernel_adjunction_arrow_func C S t T0 Q))
  (@diagram_family_transf (Functor_cat WalkingArrow_cat C) WalkingArrow_cat C (@comp_cat_fapp0 (Functor_cat
  WalkingArrow_cat C) C (Functor_cat WalkingArrow_cat C) (@initial_arrow_diagram_func C t T0) (@fapp0 (Functor_cat
  (Functor_cat WalkingArrow_cat C) (Functor_cat WalkingArrow_cat C)) (Functor_cat (Functor_cat WalkingArrow_cat C) C)
  (@comp_cat_cov_func (Functor_cat WalkingArrow_cat C) (Functor_cat WalkingArrow_cat C) C (@kernel_adjunction_func C S
  t T P)) (@cokernel_adjunction_arrow_func C S t T0 Q))) walking_arrow_src walking_arrow_tgt walking_arrow_generator)
  (@diagram_family_transf (Functor_cat WalkingArrow_cat C) WalkingArrow_cat C (@comp_cat_fapp0 (Functor_cat
  WalkingArrow_cat C) C (Functor_cat WalkingArrow_cat C) (@terminal_arrow_diagram_func C t T) (@kernel_adjunction_func
  C S t T P)) walking_arrow_src walking_arrow_tgt walking_arrow_generator))) walking_arrow_src)
  (@one_cat_kernel_family_projection_precomp_path (Functor_cat WalkingArrow_cat C) C S C1 t T P
  (@kernel_adjunction_func C S t T P) (@diagram_evaluation_at_func WalkingArrow_cat C walking_arrow_src)
  (@cokernel_adjunction_arrow_func C S t T0 Q) (@kernel_adjunction_inclusion C S t T P)
  (@one_cat_adjunction_source_to_image C S C1 t T T0 P Q))
      (@eq_trans (@Transf (Functor_cat WalkingArrow_cat C) C (@kernel_adjunction_func C S t T P)
        (@diagram_evaluation_at_func WalkingArrow_cat C walking_arrow_tgt)) (@comp_fapp0 (Functor_cat (Functor_cat
        WalkingArrow_cat C) C) (@kernel_adjunction_func C S t T P) (@diagram_evaluation_at_func WalkingArrow_cat C
        walking_arrow_src) (@diagram_evaluation_at_func WalkingArrow_cat C walking_arrow_tgt)
        (@sym_transf_tapp0_transf (Functor_cat WalkingArrow_cat C) WalkingArrow_cat C (@fapp0 (Functor_cat
        (Functor_cat WalkingArrow_cat C) C) (Functor_cat (Functor_cat WalkingArrow_cat C) (Functor_cat
        WalkingArrow_cat C)) (@comp_cat_cov_func (Functor_cat WalkingArrow_cat C) C (Functor_cat WalkingArrow_cat C)
        (@terminal_arrow_diagram_func C t T)) (@diagram_evaluation_at_func WalkingArrow_cat C walking_arrow_src))
        (@cokernel_adjunction_arrow_func C S t T0 Q) (@fapp0 _ _ (@adjunction_untranspose_func (Functor_cat
        (Functor_cat WalkingArrow_cat C) C) (Functor_cat (Functor_cat WalkingArrow_cat C) (Functor_cat
        WalkingArrow_cat C)) (@comp_cat_cov_func (Functor_cat WalkingArrow_cat C) C (Functor_cat WalkingArrow_cat C)
        (@terminal_arrow_diagram_func C t T)) (@comp_cat_cov_func (Functor_cat WalkingArrow_cat C) (Functor_cat
        WalkingArrow_cat C) C (@kernel_adjunction_func C S t T P)) (@one_cat_postcomp_adjunction (Functor_cat
        WalkingArrow_cat C) C (Functor_cat WalkingArrow_cat C) C1 (@one_cat_functor_category WalkingArrow_cat C C1)
        (@terminal_arrow_diagram_func C t T) (@kernel_adjunction_func C S t T P) (@kernel_adjunction_evidence C S t T
        P)) (@diagram_evaluation_at_func WalkingArrow_cat C walking_arrow_src) (@cokernel_adjunction_arrow_func C S t
        T0 Q)) (@one_cat_adjunction_source_to_image C S C1 t T T0 P Q)) walking_arrow_src)
        (@kernel_adjunction_inclusion C S t T P)) (@comp_fapp0 (Functor_cat (Functor_cat WalkingArrow_cat C) C)
        (@kernel_adjunction_func C S t T P) (@diagram_evaluation_at_func WalkingArrow_cat C walking_arrow_src)
        (@diagram_evaluation_at_func WalkingArrow_cat C walking_arrow_tgt) (@diagram_evaluation_transf
        WalkingArrow_cat C walking_arrow_src walking_arrow_tgt walking_arrow_generator) (@kernel_adjunction_inclusion
        C S t T P)) (@sym_transf_tapp0_transf (Functor_cat WalkingArrow_cat C) WalkingArrow_cat C (@fapp0 (Functor_cat
        (Functor_cat WalkingArrow_cat C) C) (Functor_cat (Functor_cat WalkingArrow_cat C) (Functor_cat
        WalkingArrow_cat C)) (@comp_cat_cov_func (Functor_cat WalkingArrow_cat C) C (Functor_cat WalkingArrow_cat C)
        (@terminal_arrow_diagram_func C t T)) (@kernel_adjunction_func C S t T P)) (@cokernel_adjunction_arrow_func C
        S t T0 Q) (@fapp0 _ _ (@adjunction_untranspose_func (Functor_cat (Functor_cat WalkingArrow_cat C) C)
        (Functor_cat (Functor_cat WalkingArrow_cat C) (Functor_cat WalkingArrow_cat C)) (@comp_cat_cov_func
        (Functor_cat WalkingArrow_cat C) C (Functor_cat WalkingArrow_cat C) (@terminal_arrow_diagram_func C t T))
        (@comp_cat_cov_func (Functor_cat WalkingArrow_cat C) (Functor_cat WalkingArrow_cat C) C
        (@kernel_adjunction_func C S t T P)) (@one_cat_postcomp_adjunction (Functor_cat WalkingArrow_cat C) C
        (Functor_cat WalkingArrow_cat C) C1 (@one_cat_functor_category WalkingArrow_cat C C1)
        (@terminal_arrow_diagram_func C t T) (@kernel_adjunction_func C S t T P) (@kernel_adjunction_evidence C S t T
        P)) (@kernel_adjunction_func C S t T P) (@cokernel_adjunction_arrow_func C S t T0 Q)) (@comp_fapp0
        (Functor_cat (Functor_cat WalkingArrow_cat C) C) (@kernel_adjunction_func C S t T P) (@Const_func (Functor_cat
        WalkingArrow_cat C) C t) (@fapp0 (Functor_cat (Functor_cat WalkingArrow_cat C) (Functor_cat WalkingArrow_cat
        C)) (Functor_cat (Functor_cat WalkingArrow_cat C) C) (@comp_cat_cov_func (Functor_cat WalkingArrow_cat C)
        (Functor_cat WalkingArrow_cat C) C (@kernel_adjunction_func C S t T P)) (@cokernel_adjunction_arrow_func C S t
        T0 Q)) (@diagram_family_transf (Functor_cat WalkingArrow_cat C) WalkingArrow_cat C (@comp_cat_fapp0
        (Functor_cat WalkingArrow_cat C) C (Functor_cat WalkingArrow_cat C) (@initial_arrow_diagram_func C t T0)
        (@fapp0 (Functor_cat (Functor_cat WalkingArrow_cat C) (Functor_cat WalkingArrow_cat C)) (Functor_cat
        (Functor_cat WalkingArrow_cat C) C) (@comp_cat_cov_func (Functor_cat WalkingArrow_cat C) (Functor_cat
        WalkingArrow_cat C) C (@kernel_adjunction_func C S t T P)) (@cokernel_adjunction_arrow_func C S t T0 Q)))
        walking_arrow_src walking_arrow_tgt walking_arrow_generator) (@diagram_family_transf (Functor_cat
        WalkingArrow_cat C) WalkingArrow_cat C (@comp_cat_fapp0 (Functor_cat WalkingArrow_cat C) C (Functor_cat
        WalkingArrow_cat C) (@terminal_arrow_diagram_func C t T) (@kernel_adjunction_func C S t T P))
        walking_arrow_src walking_arrow_tgt walking_arrow_generator))) walking_arrow_src) (@eq_ap (@Transf
        (Functor_cat WalkingArrow_cat C) C (@diagram_evaluation_at_func WalkingArrow_cat C walking_arrow_src)
        (@diagram_evaluation_at_func WalkingArrow_cat C walking_arrow_tgt)) (@Transf (Functor_cat WalkingArrow_cat C)
        C (@kernel_adjunction_func C S t T P) (@diagram_evaluation_at_func WalkingArrow_cat C walking_arrow_tgt)) (λ d
        : τ (@Transf (Functor_cat WalkingArrow_cat C) C (@diagram_evaluation_at_func WalkingArrow_cat C
        walking_arrow_src) (@diagram_evaluation_at_func WalkingArrow_cat C walking_arrow_tgt)), @comp_fapp0
        (Functor_cat (Functor_cat WalkingArrow_cat C) C) (@kernel_adjunction_func C S t T P)
        (@diagram_evaluation_at_func WalkingArrow_cat C walking_arrow_src) (@diagram_evaluation_at_func
        WalkingArrow_cat C walking_arrow_tgt) d (@kernel_adjunction_inclusion C S t T P))
      (@sym_transf_tapp0_transf (Functor_cat WalkingArrow_cat C) WalkingArrow_cat C (@fapp0 (Functor_cat (Functor_cat
        WalkingArrow_cat C) C) (Functor_cat (Functor_cat WalkingArrow_cat C) (Functor_cat WalkingArrow_cat C))
        (@comp_cat_cov_func (Functor_cat WalkingArrow_cat C) C (Functor_cat WalkingArrow_cat C)
        (@terminal_arrow_diagram_func C t T)) (@diagram_evaluation_at_func WalkingArrow_cat C walking_arrow_src))
        (@cokernel_adjunction_arrow_func C S t T0 Q) (@fapp0 _ _ (@adjunction_untranspose_func (Functor_cat
        (Functor_cat WalkingArrow_cat C) C) (Functor_cat (Functor_cat WalkingArrow_cat C) (Functor_cat
        WalkingArrow_cat C)) (@comp_cat_cov_func (Functor_cat WalkingArrow_cat C) C (Functor_cat WalkingArrow_cat C)
        (@terminal_arrow_diagram_func C t T)) (@comp_cat_cov_func (Functor_cat WalkingArrow_cat C) (Functor_cat
        WalkingArrow_cat C) C (@kernel_adjunction_func C S t T P)) (@one_cat_postcomp_adjunction (Functor_cat
        WalkingArrow_cat C) C (Functor_cat WalkingArrow_cat C) C1 (@one_cat_functor_category WalkingArrow_cat C C1)
        (@terminal_arrow_diagram_func C t T) (@kernel_adjunction_func C S t T P) (@kernel_adjunction_evidence C S t T
        P)) (@diagram_evaluation_at_func WalkingArrow_cat C walking_arrow_src) (@cokernel_adjunction_arrow_func C S t
        T0 Q)) (@one_cat_adjunction_source_to_image C S C1 t T T0 P Q)) walking_arrow_src) (@diagram_evaluation_transf
        WalkingArrow_cat C walking_arrow_src walking_arrow_tgt walking_arrow_generator)
        (@one_cat_source_to_image_projection_path C S C1 t T T0 P Q))
        (@eq_trans (@Transf (Functor_cat WalkingArrow_cat C) C (@kernel_adjunction_func C S t T P)
          (@diagram_evaluation_at_func WalkingArrow_cat C walking_arrow_tgt)) (@comp_fapp0 (Functor_cat (Functor_cat
          WalkingArrow_cat C) C) (@kernel_adjunction_func C S t T P) (@diagram_evaluation_at_func WalkingArrow_cat C
          walking_arrow_src) (@diagram_evaluation_at_func WalkingArrow_cat C walking_arrow_tgt)
          (@diagram_evaluation_transf WalkingArrow_cat C walking_arrow_src walking_arrow_tgt walking_arrow_generator)
          (@kernel_adjunction_inclusion C S t T P)) (@comp_fapp0 (Functor_cat (Functor_cat WalkingArrow_cat C) C)
          (@kernel_adjunction_func C S t T P) (@Const_func (Functor_cat WalkingArrow_cat C) C t)
          (@diagram_evaluation_at_func WalkingArrow_cat C walking_arrow_tgt) (@diagram_family_transf (Functor_cat
          WalkingArrow_cat C) WalkingArrow_cat C (@comp_cat_fapp0 (Functor_cat WalkingArrow_cat C) C (Functor_cat
          WalkingArrow_cat C) (@initial_arrow_diagram_func C t T0) (@diagram_evaluation_at_func WalkingArrow_cat C
          walking_arrow_tgt)) walking_arrow_src walking_arrow_tgt walking_arrow_generator) (@diagram_family_transf
          (Functor_cat WalkingArrow_cat C) WalkingArrow_cat C (@comp_cat_fapp0 (Functor_cat WalkingArrow_cat C) C
          (Functor_cat WalkingArrow_cat C) (@terminal_arrow_diagram_func C t T) (@kernel_adjunction_func C S t T P))
          walking_arrow_src walking_arrow_tgt walking_arrow_generator)) (@sym_transf_tapp0_transf (Functor_cat
          WalkingArrow_cat C) WalkingArrow_cat C (@fapp0 (Functor_cat (Functor_cat WalkingArrow_cat C) C) (Functor_cat
          (Functor_cat WalkingArrow_cat C) (Functor_cat WalkingArrow_cat C)) (@comp_cat_cov_func (Functor_cat
          WalkingArrow_cat C) C (Functor_cat WalkingArrow_cat C) (@terminal_arrow_diagram_func C t T))
          (@kernel_adjunction_func C S t T P)) (@cokernel_adjunction_arrow_func C S t T0 Q) (@fapp0 _ _
          (@adjunction_untranspose_func (Functor_cat (Functor_cat WalkingArrow_cat C) C) (Functor_cat (Functor_cat
          WalkingArrow_cat C) (Functor_cat WalkingArrow_cat C)) (@comp_cat_cov_func (Functor_cat WalkingArrow_cat C) C
          (Functor_cat WalkingArrow_cat C) (@terminal_arrow_diagram_func C t T)) (@comp_cat_cov_func (Functor_cat
          WalkingArrow_cat C) (Functor_cat WalkingArrow_cat C) C (@kernel_adjunction_func C S t T P))
          (@one_cat_postcomp_adjunction (Functor_cat WalkingArrow_cat C) C (Functor_cat WalkingArrow_cat C) C1
          (@one_cat_functor_category WalkingArrow_cat C C1) (@terminal_arrow_diagram_func C t T)
          (@kernel_adjunction_func C S t T P) (@kernel_adjunction_evidence C S t T P)) (@kernel_adjunction_func C S t
          T P) (@cokernel_adjunction_arrow_func C S t T0 Q)) (@comp_fapp0 (Functor_cat (Functor_cat WalkingArrow_cat
          C) C) (@kernel_adjunction_func C S t T P) (@Const_func (Functor_cat WalkingArrow_cat C) C t) (@fapp0
          (Functor_cat (Functor_cat WalkingArrow_cat C) (Functor_cat WalkingArrow_cat C)) (Functor_cat (Functor_cat
          WalkingArrow_cat C) C) (@comp_cat_cov_func (Functor_cat WalkingArrow_cat C) (Functor_cat WalkingArrow_cat C)
          C (@kernel_adjunction_func C S t T P)) (@cokernel_adjunction_arrow_func C S t T0 Q)) (@diagram_family_transf
          (Functor_cat WalkingArrow_cat C) WalkingArrow_cat C (@comp_cat_fapp0 (Functor_cat WalkingArrow_cat C) C
          (Functor_cat WalkingArrow_cat C) (@initial_arrow_diagram_func C t T0) (@fapp0 (Functor_cat (Functor_cat
          WalkingArrow_cat C) (Functor_cat WalkingArrow_cat C)) (Functor_cat (Functor_cat WalkingArrow_cat C) C)
          (@comp_cat_cov_func (Functor_cat WalkingArrow_cat C) (Functor_cat WalkingArrow_cat C) C
          (@kernel_adjunction_func C S t T P)) (@cokernel_adjunction_arrow_func C S t T0 Q))) walking_arrow_src
          walking_arrow_tgt walking_arrow_generator) (@diagram_family_transf (Functor_cat WalkingArrow_cat C)
          WalkingArrow_cat C (@comp_cat_fapp0 (Functor_cat WalkingArrow_cat C) C (Functor_cat WalkingArrow_cat C)
          (@terminal_arrow_diagram_func C t T) (@kernel_adjunction_func C S t T P)) walking_arrow_src
          walking_arrow_tgt walking_arrow_generator))) walking_arrow_src) (@one_cat_kernel_whole_annihilation C S C1 t
          T T0 P) (@eq_sym (@Transf (Functor_cat WalkingArrow_cat C) C (@kernel_adjunction_func C S t T P)
          (@diagram_evaluation_at_func WalkingArrow_cat C walking_arrow_tgt)) (@sym_transf_tapp0_transf (Functor_cat
          WalkingArrow_cat C) WalkingArrow_cat C (@fapp0 (Functor_cat (Functor_cat WalkingArrow_cat C) C) (Functor_cat
          (Functor_cat WalkingArrow_cat C) (Functor_cat WalkingArrow_cat C)) (@comp_cat_cov_func (Functor_cat
          WalkingArrow_cat C) C (Functor_cat WalkingArrow_cat C) (@terminal_arrow_diagram_func C t T))
          (@kernel_adjunction_func C S t T P)) (@cokernel_adjunction_arrow_func C S t T0 Q) (@fapp0 _ _
          (@adjunction_untranspose_func (Functor_cat (Functor_cat WalkingArrow_cat C) C) (Functor_cat (Functor_cat
          WalkingArrow_cat C) (Functor_cat WalkingArrow_cat C)) (@comp_cat_cov_func (Functor_cat WalkingArrow_cat C) C
          (Functor_cat WalkingArrow_cat C) (@terminal_arrow_diagram_func C t T)) (@comp_cat_cov_func (Functor_cat
          WalkingArrow_cat C) (Functor_cat WalkingArrow_cat C) C (@kernel_adjunction_func C S t T P))
          (@one_cat_postcomp_adjunction (Functor_cat WalkingArrow_cat C) C (Functor_cat WalkingArrow_cat C) C1
          (@one_cat_functor_category WalkingArrow_cat C C1) (@terminal_arrow_diagram_func C t T)
          (@kernel_adjunction_func C S t T P) (@kernel_adjunction_evidence C S t T P)) (@kernel_adjunction_func C S t
          T P) (@cokernel_adjunction_arrow_func C S t T0 Q)) (@comp_fapp0 (Functor_cat (Functor_cat WalkingArrow_cat
          C) C) (@kernel_adjunction_func C S t T P) (@Const_func (Functor_cat WalkingArrow_cat C) C t) (@fapp0
          (Functor_cat (Functor_cat WalkingArrow_cat C) (Functor_cat WalkingArrow_cat C)) (Functor_cat (Functor_cat
          WalkingArrow_cat C) C) (@comp_cat_cov_func (Functor_cat WalkingArrow_cat C) (Functor_cat WalkingArrow_cat C)
          C (@kernel_adjunction_func C S t T P)) (@cokernel_adjunction_arrow_func C S t T0 Q)) (@diagram_family_transf
          (Functor_cat WalkingArrow_cat C) WalkingArrow_cat C (@comp_cat_fapp0 (Functor_cat WalkingArrow_cat C) C
          (Functor_cat WalkingArrow_cat C) (@initial_arrow_diagram_func C t T0) (@fapp0 (Functor_cat (Functor_cat
          WalkingArrow_cat C) (Functor_cat WalkingArrow_cat C)) (Functor_cat (Functor_cat WalkingArrow_cat C) C)
          (@comp_cat_cov_func (Functor_cat WalkingArrow_cat C) (Functor_cat WalkingArrow_cat C) C
          (@kernel_adjunction_func C S t T P)) (@cokernel_adjunction_arrow_func C S t T0 Q))) walking_arrow_src
          walking_arrow_tgt walking_arrow_generator) (@diagram_family_transf (Functor_cat WalkingArrow_cat C)
          WalkingArrow_cat C (@comp_cat_fapp0 (Functor_cat WalkingArrow_cat C) C (Functor_cat WalkingArrow_cat C)
          (@terminal_arrow_diagram_func C t T) (@kernel_adjunction_func C S t T P)) walking_arrow_src
          walking_arrow_tgt walking_arrow_generator))) walking_arrow_src) (@comp_fapp0 (Functor_cat (Functor_cat
          WalkingArrow_cat C) C) (@kernel_adjunction_func C S t T P) (@Const_func (Functor_cat WalkingArrow_cat C) C
          t) (@diagram_evaluation_at_func WalkingArrow_cat C walking_arrow_tgt) (@diagram_family_transf (Functor_cat
          WalkingArrow_cat C) WalkingArrow_cat C (@comp_cat_fapp0 (Functor_cat WalkingArrow_cat C) C (Functor_cat
          WalkingArrow_cat C) (@initial_arrow_diagram_func C t T0) (@diagram_evaluation_at_func WalkingArrow_cat C
          walking_arrow_tgt)) walking_arrow_src walking_arrow_tgt walking_arrow_generator) (@diagram_family_transf
          (Functor_cat WalkingArrow_cat C) WalkingArrow_cat C (@comp_cat_fapp0 (Functor_cat WalkingArrow_cat C) C
          (Functor_cat WalkingArrow_cat C) (@terminal_arrow_diagram_func C t T) (@kernel_adjunction_func C S t T P))
          walking_arrow_src walking_arrow_tgt walking_arrow_generator)) (@one_cat_kernel_family_projection_zero_path
          (Functor_cat WalkingArrow_cat C) C S C1 t T T0 P (@kernel_adjunction_func C S t T P)
          (@cokernel_adjunction_arrow_func C S t T0 Q))))));

// Build one native square in Functor_cat(D,C) from the derived whole cell u∘κ=0.
// Realize and exchange it, then normalize its initial column. No caller square
// or per-object cone data is required.
symbol one_cat_coimage_image_mate_input [C : Cat] [S : τ (@PreadditiveCategory C)]
  (C1 : τ (IsNCat (cat_succ cat_zero) C)) [t : τ (Obj C)]
  (T : τ (@TerminalObject C t)) (T0 : τ (@TerminalObject (Op_cat C) t))
  (P : τ (@KernelAdjunctionStructure C S t T)) (Q : τ (@CokernelAdjunctionStructure C S t T0))
  : τ (@Transf (Functor_cat WalkingArrow_cat C) (Functor_cat WalkingArrow_cat C) (@kernel_adjunction_arrow_func C S t
    T P) (@comp_cat_fapp0 (Functor_cat WalkingArrow_cat C) C (Functor_cat WalkingArrow_cat C)
    (@initial_arrow_diagram_func C t T0) (@fapp0 (Functor_cat (Functor_cat WalkingArrow_cat C) (Functor_cat
    WalkingArrow_cat C)) (Functor_cat (Functor_cat WalkingArrow_cat C) C) (@comp_cat_cov_func (Functor_cat
    WalkingArrow_cat C) (Functor_cat WalkingArrow_cat C) C (@kernel_adjunction_func C S t T P))
    (@cokernel_adjunction_arrow_func C S t T0 Q))))
≔ @one_cat_cokernel_family_introduced_input (Functor_cat WalkingArrow_cat C) C C1 t T T0
    (@kernel_adjunction_func C S t T P)
    (@diagram_evaluation_at_func WalkingArrow_cat C walking_arrow_src)
    (@fapp0 _ _ (@comp_cat_cov_func (Functor_cat WalkingArrow_cat C) (Functor_cat WalkingArrow_cat C) C
      (@kernel_adjunction_func C S t T P)) (@cokernel_adjunction_arrow_func C S t T0 Q))
    (@kernel_adjunction_inclusion C S t T P) (@one_cat_adjunction_source_to_image C S C1 t T T0 P Q)
    (@one_cat_source_to_image_kills_kernel_path C S C1 t T T0 P Q);

// The canonical a:Coim⇒Im is the original whole cokernel mate of that input.
symbol one_cat_coimage_image_comparison [C : Cat] [S : τ (@PreadditiveCategory C)]
  (C1 : τ (IsNCat (cat_succ cat_zero) C)) [t : τ (Obj C)]
  (T : τ (@TerminalObject C t)) (T0 : τ (@TerminalObject (Op_cat C) t))
  (P : τ (@KernelAdjunctionStructure C S t T)) (Q : τ (@CokernelAdjunctionStructure C S t T0))
  : τ (@Transf (Functor_cat WalkingArrow_cat C) C (@adjunction_coimage_func C S t T T0 P Q) (@adjunction_image_func C
    S t T T0 P Q))
≔ @fapp0 _ _ (@one_cat_adjunction_family_untranspose_func (Functor_cat WalkingArrow_cat C) (Functor_cat
  WalkingArrow_cat C) C
    (@one_cat_functor_category WalkingArrow_cat C C1) C1
    (@cokernel_adjunction_func C S t T0 Q) (@initial_arrow_diagram_func C t T0) (@cokernel_adjunction_evidence C S t
      T0 Q) (@kernel_adjunction_arrow_func C S t T P) (@fapp0 (Functor_cat (Functor_cat WalkingArrow_cat C)
      (Functor_cat WalkingArrow_cat C)) (Functor_cat (Functor_cat WalkingArrow_cat C) C) (@comp_cat_cov_func
      (Functor_cat WalkingArrow_cat C) (Functor_cat WalkingArrow_cat C) C (@kernel_adjunction_func C S t T P))
      (@cokernel_adjunction_arrow_func C S t T0 Q)))
    (@one_cat_coimage_image_mate_input C S C1 t T T0 P Q);

// The constructed input retains u as its entire target transformation.
symbol one_cat_coimage_image_input_target_path [C : Cat] [S : τ (@PreadditiveCategory C)]
  (C1 : τ (IsNCat (cat_succ cat_zero) C)) [t : τ (Obj C)]
  (T : τ (@TerminalObject C t)) (T0 : τ (@TerminalObject (Op_cat C) t))
  (P : τ (@KernelAdjunctionStructure C S t T)) (Q : τ (@CokernelAdjunctionStructure C S t T0))
  : τ (@= (@Transf (Functor_cat WalkingArrow_cat C) C (@diagram_evaluation_at_func WalkingArrow_cat C
    walking_arrow_src) (@fapp0 (Functor_cat (Functor_cat WalkingArrow_cat C) (Functor_cat WalkingArrow_cat C))
    (Functor_cat (Functor_cat WalkingArrow_cat C) C) (@comp_cat_cov_func (Functor_cat WalkingArrow_cat C) (Functor_cat
    WalkingArrow_cat C) C (@kernel_adjunction_func C S t T P)) (@cokernel_adjunction_arrow_func C S t T0 Q)))
      (@sym_transf_tapp0_transf (Functor_cat WalkingArrow_cat C) WalkingArrow_cat C (@kernel_adjunction_arrow_func C S
        t T P) (@comp_cat_fapp0 (Functor_cat WalkingArrow_cat C) C (Functor_cat WalkingArrow_cat C)
        (@initial_arrow_diagram_func C t T0) (@fapp0 (Functor_cat (Functor_cat WalkingArrow_cat C) (Functor_cat
        WalkingArrow_cat C)) (Functor_cat (Functor_cat WalkingArrow_cat C) C) (@comp_cat_cov_func (Functor_cat
        WalkingArrow_cat C) (Functor_cat WalkingArrow_cat C) C (@kernel_adjunction_func C S t T P))
        (@cokernel_adjunction_arrow_func C S t T0 Q))) (@one_cat_coimage_image_mate_input C S C1 t T T0 P Q)
        walking_arrow_tgt) (@one_cat_adjunction_source_to_image C S C1 t T T0 P Q))
≔ @one_cat_cokernel_family_introduced_target_path (Functor_cat WalkingArrow_cat C) C C1 t T T0
    (@kernel_adjunction_func C S t T P)
    (@diagram_evaluation_at_func WalkingArrow_cat C walking_arrow_src)
    (@fapp0 _ _ (@comp_cat_cov_func (Functor_cat WalkingArrow_cat C) (Functor_cat WalkingArrow_cat C) C
      (@kernel_adjunction_func C S t T P)) (@cokernel_adjunction_arrow_func C S t T0 Q))
    (@kernel_adjunction_inclusion C S t T P) (@one_cat_adjunction_source_to_image C S C1 t T T0 P Q)
    (@one_cat_source_to_image_kills_kernel_path C S C1 t T T0 P Q);

// Observe a supplied whole b by E₀(unmate_P(E₁(transpose_Q(b)))).
// This is a function on whole transformations, not a new categorical primitive
// or a separately packaged internal functor in b.
symbol one_cat_coimage_image_factorization_value [C : Cat] [S : τ (@PreadditiveCategory C)]
  (C1 : τ (IsNCat (cat_succ cat_zero) C)) [t : τ (Obj C)]
  (T : τ (@TerminalObject C t)) (T0 : τ (@TerminalObject (Op_cat C) t))
  (P : τ (@KernelAdjunctionStructure C S t T)) (Q : τ (@CokernelAdjunctionStructure C S t T0)) (b : τ (@Transf
    (Functor_cat WalkingArrow_cat C) C (@fapp0 (Functor_cat (Functor_cat WalkingArrow_cat C) (Functor_cat
    WalkingArrow_cat C)) (Functor_cat (Functor_cat WalkingArrow_cat C) C) (@comp_cat_cov_func (Functor_cat
    WalkingArrow_cat C) (Functor_cat WalkingArrow_cat C) C (@cokernel_adjunction_func C S t T0 Q))
    (@kernel_adjunction_arrow_func C S t T P)) (@fapp0 (Functor_cat (Functor_cat WalkingArrow_cat C) (Functor_cat
    WalkingArrow_cat C)) (Functor_cat (Functor_cat WalkingArrow_cat C) C) (@comp_cat_cov_func (Functor_cat
    WalkingArrow_cat C) (Functor_cat WalkingArrow_cat C) C (@kernel_adjunction_func C S t T P))
    (@cokernel_adjunction_arrow_func C S t T0 Q))))
  : τ (@Transf (Functor_cat WalkingArrow_cat C) C (@diagram_evaluation_at_func WalkingArrow_cat C walking_arrow_src)
    (@diagram_evaluation_at_func WalkingArrow_cat C walking_arrow_tgt))
≔ (@sym_transf_tapp0_transf (Functor_cat WalkingArrow_cat C) WalkingArrow_cat C (@comp_cat_fapp0 (Functor_cat
  WalkingArrow_cat C) C (Functor_cat WalkingArrow_cat C) (@terminal_arrow_diagram_func C t T)
  (@diagram_evaluation_at_func WalkingArrow_cat C walking_arrow_src)) (@cokernel_adjunction_arrow_func C S t T0 Q)
  (@fapp0 _ _ (@one_cat_adjunction_family_untranspose_func (Functor_cat WalkingArrow_cat C) C (Functor_cat
  WalkingArrow_cat C) C1 (@one_cat_functor_category WalkingArrow_cat C C1) (@terminal_arrow_diagram_func C t T)
  (@kernel_adjunction_func C S t T P) (@kernel_adjunction_evidence C S t T P) (@diagram_evaluation_at_func
  WalkingArrow_cat C walking_arrow_src) (@cokernel_adjunction_arrow_func C S t T0 Q)) (@sym_transf_tapp0_transf
  (Functor_cat WalkingArrow_cat C) WalkingArrow_cat C (@kernel_adjunction_arrow_func C S t T P) (@comp_cat_fapp0
  (Functor_cat WalkingArrow_cat C) C (Functor_cat WalkingArrow_cat C) (@initial_arrow_diagram_func C t T0) (@fapp0
  (Functor_cat (Functor_cat WalkingArrow_cat C) (Functor_cat WalkingArrow_cat C)) (Functor_cat (Functor_cat
  WalkingArrow_cat C) C) (@comp_cat_cov_func (Functor_cat WalkingArrow_cat C) (Functor_cat WalkingArrow_cat C) C
  (@kernel_adjunction_func C S t T P)) (@cokernel_adjunction_arrow_func C S t T0 Q))) (@fapp0 _ _
  (@one_cat_adjunction_family_transpose_func (Functor_cat WalkingArrow_cat C) (Functor_cat WalkingArrow_cat C) C
  (@one_cat_functor_category WalkingArrow_cat C C1) C1 (@cokernel_adjunction_func C S t T0 Q)
  (@initial_arrow_diagram_func C t T0) (@cokernel_adjunction_evidence C S t T0 Q) (@kernel_adjunction_arrow_func C S t
  T P) (@fapp0 (Functor_cat (Functor_cat WalkingArrow_cat C) (Functor_cat WalkingArrow_cat C)) (Functor_cat
  (Functor_cat WalkingArrow_cat C) C) (@comp_cat_cov_func (Functor_cat WalkingArrow_cat C) (Functor_cat
  WalkingArrow_cat C) C (@kernel_adjunction_func C S t T P)) (@cokernel_adjunction_arrow_func C S t T0 Q))) b)
  walking_arrow_tgt)) walking_arrow_src);

// The actual comparison reconstructs the entire universal differential ∂.
symbol one_cat_coimage_image_factorization_path [C : Cat] [S : τ (@PreadditiveCategory C)]
  (C1 : τ (IsNCat (cat_succ cat_zero) C)) [t : τ (Obj C)]
  (T : τ (@TerminalObject C t)) (T0 : τ (@TerminalObject (Op_cat C) t))
  (P : τ (@KernelAdjunctionStructure C S t T)) (Q : τ (@CokernelAdjunctionStructure C S t T0))
  : τ (@= (@Transf (Functor_cat WalkingArrow_cat C) C (@diagram_evaluation_at_func WalkingArrow_cat C
    walking_arrow_src) (@diagram_evaluation_at_func WalkingArrow_cat C walking_arrow_tgt))
    (@one_cat_coimage_image_factorization_value C S C1 t T T0 P Q (@one_cat_coimage_image_comparison C S C1 t T T0 P
    Q)) (@diagram_evaluation_transf WalkingArrow_cat C walking_arrow_src walking_arrow_tgt walking_arrow_generator))
≔ @eq_trans (@Transf (Functor_cat WalkingArrow_cat C) C (@diagram_evaluation_at_func WalkingArrow_cat C
  walking_arrow_src) (@diagram_evaluation_at_func WalkingArrow_cat C walking_arrow_tgt))
  (@one_cat_coimage_image_factorization_value C S C1 t T T0 P Q (@one_cat_coimage_image_comparison C S C1 t T T0 P Q))
  (@sym_transf_tapp0_transf (Functor_cat WalkingArrow_cat C) WalkingArrow_cat C (@comp_cat_fapp0 (Functor_cat
  WalkingArrow_cat C) C (Functor_cat WalkingArrow_cat C) (@terminal_arrow_diagram_func C t T)
  (@diagram_evaluation_at_func WalkingArrow_cat C walking_arrow_src)) (@cokernel_adjunction_arrow_func C S t T0 Q)
  (@fapp0 _ _ (@one_cat_adjunction_family_untranspose_func (Functor_cat WalkingArrow_cat C) C (Functor_cat
  WalkingArrow_cat C) C1 (@one_cat_functor_category WalkingArrow_cat C C1) (@terminal_arrow_diagram_func C t T)
  (@kernel_adjunction_func C S t T P) (@kernel_adjunction_evidence C S t T P) (@diagram_evaluation_at_func
  WalkingArrow_cat C walking_arrow_src) (@cokernel_adjunction_arrow_func C S t T0 Q))
  (@one_cat_adjunction_source_to_image C S C1 t T T0 P Q)) walking_arrow_src) (@diagram_evaluation_transf
  WalkingArrow_cat C walking_arrow_src walking_arrow_tgt walking_arrow_generator) (@eq_ap (@Transf (Functor_cat
  WalkingArrow_cat C) C (@diagram_evaluation_at_func WalkingArrow_cat C walking_arrow_src) (@fapp0 (Functor_cat
  (Functor_cat WalkingArrow_cat C) (Functor_cat WalkingArrow_cat C)) (Functor_cat (Functor_cat WalkingArrow_cat C) C)
  (@comp_cat_cov_func (Functor_cat WalkingArrow_cat C) (Functor_cat WalkingArrow_cat C) C (@kernel_adjunction_func C S
  t T P)) (@cokernel_adjunction_arrow_func C S t T0 Q))) (@Transf (Functor_cat WalkingArrow_cat C) C
  (@diagram_evaluation_at_func WalkingArrow_cat C walking_arrow_src) (@diagram_evaluation_at_func WalkingArrow_cat C
  walking_arrow_tgt)) (λ x : τ (@Transf (Functor_cat WalkingArrow_cat C) C (@diagram_evaluation_at_func
  WalkingArrow_cat C walking_arrow_src) (@fapp0 (Functor_cat (Functor_cat WalkingArrow_cat C) (Functor_cat
  WalkingArrow_cat C)) (Functor_cat (Functor_cat WalkingArrow_cat C) C) (@comp_cat_cov_func (Functor_cat
  WalkingArrow_cat C) (Functor_cat WalkingArrow_cat C) C (@kernel_adjunction_func C S t T P))
  (@cokernel_adjunction_arrow_func C S t T0 Q))), (@sym_transf_tapp0_transf (Functor_cat WalkingArrow_cat C)
  WalkingArrow_cat C (@comp_cat_fapp0 (Functor_cat WalkingArrow_cat C) C (Functor_cat WalkingArrow_cat C)
  (@terminal_arrow_diagram_func C t T) (@diagram_evaluation_at_func WalkingArrow_cat C walking_arrow_src))
  (@cokernel_adjunction_arrow_func C S t T0 Q) (@fapp0 _ _ (@one_cat_adjunction_family_untranspose_func (Functor_cat
  WalkingArrow_cat C) C (Functor_cat WalkingArrow_cat C) C1 (@one_cat_functor_category WalkingArrow_cat C C1)
  (@terminal_arrow_diagram_func C t T) (@kernel_adjunction_func C S t T P) (@kernel_adjunction_evidence C S t T P)
  (@diagram_evaluation_at_func WalkingArrow_cat C walking_arrow_src) (@cokernel_adjunction_arrow_func C S t T0 Q)) x)
  walking_arrow_src)) (@sym_transf_tapp0_transf (Functor_cat WalkingArrow_cat C) WalkingArrow_cat C
  (@kernel_adjunction_arrow_func C S t T P) (@comp_cat_fapp0 (Functor_cat WalkingArrow_cat C) C (Functor_cat
  WalkingArrow_cat C) (@initial_arrow_diagram_func C t T0) (@fapp0 (Functor_cat (Functor_cat WalkingArrow_cat C)
  (Functor_cat WalkingArrow_cat C)) (Functor_cat (Functor_cat WalkingArrow_cat C) C) (@comp_cat_cov_func (Functor_cat
  WalkingArrow_cat C) (Functor_cat WalkingArrow_cat C) C (@kernel_adjunction_func C S t T P))
  (@cokernel_adjunction_arrow_func C S t T0 Q))) (@fapp0 _ _ (@one_cat_adjunction_family_transpose_func (Functor_cat
  WalkingArrow_cat C) (Functor_cat WalkingArrow_cat C) C (@one_cat_functor_category WalkingArrow_cat C C1) C1
  (@cokernel_adjunction_func C S t T0 Q) (@initial_arrow_diagram_func C t T0) (@cokernel_adjunction_evidence C S t T0
  Q) (@kernel_adjunction_arrow_func C S t T P) (@fapp0 (Functor_cat (Functor_cat WalkingArrow_cat C) (Functor_cat
  WalkingArrow_cat C)) (Functor_cat (Functor_cat WalkingArrow_cat C) C) (@comp_cat_cov_func (Functor_cat
  WalkingArrow_cat C) (Functor_cat WalkingArrow_cat C) C (@kernel_adjunction_func C S t T P))
  (@cokernel_adjunction_arrow_func C S t T0 Q))) (@one_cat_coimage_image_comparison C S C1 t T T0 P Q))
  walking_arrow_tgt) (@one_cat_adjunction_source_to_image C S C1 t T T0 P Q) (@one_cat_coimage_image_input_target_path
  C S C1 t T T0 P Q)) (@one_cat_source_to_image_projection_path C S C1 t T T0 P Q);

// The whole factorization condition determines the actual comparison uniquely.
symbol one_cat_coimage_image_factorization_unique [C : Cat] [S : τ (@PreadditiveCategory C)]
  (C1 : τ (IsNCat (cat_succ cat_zero) C)) [t : τ (Obj C)]
  (T : τ (@TerminalObject C t)) (T0 : τ (@TerminalObject (Op_cat C) t))
  (P : τ (@KernelAdjunctionStructure C S t T)) (Q : τ (@CokernelAdjunctionStructure C S t T0)) (b : τ (@Transf
    (Functor_cat WalkingArrow_cat C) C (@fapp0 (Functor_cat (Functor_cat WalkingArrow_cat C) (Functor_cat
    WalkingArrow_cat C)) (Functor_cat (Functor_cat WalkingArrow_cat C) C) (@comp_cat_cov_func (Functor_cat
    WalkingArrow_cat C) (Functor_cat WalkingArrow_cat C) C (@cokernel_adjunction_func C S t T0 Q))
    (@kernel_adjunction_arrow_func C S t T P)) (@fapp0 (Functor_cat (Functor_cat WalkingArrow_cat C) (Functor_cat
    WalkingArrow_cat C)) (Functor_cat (Functor_cat WalkingArrow_cat C) C) (@comp_cat_cov_func (Functor_cat
    WalkingArrow_cat C) (Functor_cat WalkingArrow_cat C) C (@kernel_adjunction_func C S t T P))
    (@cokernel_adjunction_arrow_func C S t T0 Q))))
  (p : τ (@= (@Transf (Functor_cat WalkingArrow_cat C) C (@diagram_evaluation_at_func WalkingArrow_cat C
    walking_arrow_src) (@diagram_evaluation_at_func WalkingArrow_cat C walking_arrow_tgt))
    (@one_cat_coimage_image_factorization_value C S C1 t T T0 P Q b) (@diagram_evaluation_transf WalkingArrow_cat C
    walking_arrow_src walking_arrow_tgt walking_arrow_generator)))
  : τ (@= (@Transf (Functor_cat WalkingArrow_cat C) C (@fapp0 (Functor_cat (Functor_cat WalkingArrow_cat C)
    (Functor_cat WalkingArrow_cat C)) (Functor_cat (Functor_cat WalkingArrow_cat C) C) (@comp_cat_cov_func
    (Functor_cat WalkingArrow_cat C) (Functor_cat WalkingArrow_cat C) C (@cokernel_adjunction_func C S t T0 Q))
    (@kernel_adjunction_arrow_func C S t T P)) (@fapp0 (Functor_cat (Functor_cat WalkingArrow_cat C) (Functor_cat
    WalkingArrow_cat C)) (Functor_cat (Functor_cat WalkingArrow_cat C) C) (@comp_cat_cov_func (Functor_cat
    WalkingArrow_cat C) (Functor_cat WalkingArrow_cat C) C (@kernel_adjunction_func C S t T P))
    (@cokernel_adjunction_arrow_func C S t T0 Q))) b (@one_cat_coimage_image_comparison C S C1 t T T0 P Q))
≔ @one_cat_cokernel_family_projection_reflect_path (Functor_cat WalkingArrow_cat C) C S C1 t T T0 Q (@fapp0
  (Functor_cat (Functor_cat WalkingArrow_cat C) (Functor_cat WalkingArrow_cat C)) (Functor_cat (Functor_cat
  WalkingArrow_cat C) C) (@comp_cat_cov_func (Functor_cat WalkingArrow_cat C) (Functor_cat WalkingArrow_cat C) C
  (@kernel_adjunction_func C S t T P)) (@cokernel_adjunction_arrow_func C S t T0 Q)) (@kernel_adjunction_arrow_func C
  S t T P) b (@one_cat_coimage_image_comparison C S C1 t T T0 P Q) (@eq_trans (@Transf (Functor_cat WalkingArrow_cat
  C) C (@diagram_evaluation_at_func WalkingArrow_cat C walking_arrow_src) (@fapp0 (Functor_cat (Functor_cat
  WalkingArrow_cat C) (Functor_cat WalkingArrow_cat C)) (Functor_cat (Functor_cat WalkingArrow_cat C) C)
  (@comp_cat_cov_func (Functor_cat WalkingArrow_cat C) (Functor_cat WalkingArrow_cat C) C (@kernel_adjunction_func C S
  t T P)) (@cokernel_adjunction_arrow_func C S t T0 Q))) (@sym_transf_tapp0_transf (Functor_cat WalkingArrow_cat C)
  WalkingArrow_cat C (@kernel_adjunction_arrow_func C S t T P) (@comp_cat_fapp0 (Functor_cat WalkingArrow_cat C) C
  (Functor_cat WalkingArrow_cat C) (@initial_arrow_diagram_func C t T0) (@fapp0 (Functor_cat (Functor_cat
  WalkingArrow_cat C) (Functor_cat WalkingArrow_cat C)) (Functor_cat (Functor_cat WalkingArrow_cat C) C)
  (@comp_cat_cov_func (Functor_cat WalkingArrow_cat C) (Functor_cat WalkingArrow_cat C) C (@kernel_adjunction_func C S
  t T P)) (@cokernel_adjunction_arrow_func C S t T0 Q))) (@fapp0 _ _ (@one_cat_adjunction_family_transpose_func
  (Functor_cat WalkingArrow_cat C) (Functor_cat WalkingArrow_cat C) C (@one_cat_functor_category WalkingArrow_cat C
  C1) C1 (@cokernel_adjunction_func C S t T0 Q) (@initial_arrow_diagram_func C t T0) (@cokernel_adjunction_evidence C
  S t T0 Q) (@kernel_adjunction_arrow_func C S t T P) (@fapp0 (Functor_cat (Functor_cat WalkingArrow_cat C)
  (Functor_cat WalkingArrow_cat C)) (Functor_cat (Functor_cat WalkingArrow_cat C) C) (@comp_cat_cov_func (Functor_cat
  WalkingArrow_cat C) (Functor_cat WalkingArrow_cat C) C (@kernel_adjunction_func C S t T P))
  (@cokernel_adjunction_arrow_func C S t T0 Q))) b) walking_arrow_tgt) (@one_cat_adjunction_source_to_image C S C1 t T
  T0 P Q) (@sym_transf_tapp0_transf (Functor_cat WalkingArrow_cat C) WalkingArrow_cat C (@kernel_adjunction_arrow_func
  C S t T P) (@comp_cat_fapp0 (Functor_cat WalkingArrow_cat C) C (Functor_cat WalkingArrow_cat C)
  (@initial_arrow_diagram_func C t T0) (@fapp0 (Functor_cat (Functor_cat WalkingArrow_cat C) (Functor_cat
  WalkingArrow_cat C)) (Functor_cat (Functor_cat WalkingArrow_cat C) C) (@comp_cat_cov_func (Functor_cat
  WalkingArrow_cat C) (Functor_cat WalkingArrow_cat C) C (@kernel_adjunction_func C S t T P))
  (@cokernel_adjunction_arrow_func C S t T0 Q))) (@fapp0 _ _ (@one_cat_adjunction_family_transpose_func (Functor_cat
  WalkingArrow_cat C) (Functor_cat WalkingArrow_cat C) C (@one_cat_functor_category WalkingArrow_cat C C1) C1
  (@cokernel_adjunction_func C S t T0 Q) (@initial_arrow_diagram_func C t T0) (@cokernel_adjunction_evidence C S t T0
  Q) (@kernel_adjunction_arrow_func C S t T P) (@fapp0 (Functor_cat (Functor_cat WalkingArrow_cat C) (Functor_cat
  WalkingArrow_cat C)) (Functor_cat (Functor_cat WalkingArrow_cat C) C) (@comp_cat_cov_func (Functor_cat
  WalkingArrow_cat C) (Functor_cat WalkingArrow_cat C) C (@kernel_adjunction_func C S t T P))
  (@cokernel_adjunction_arrow_func C S t T0 Q))) (@one_cat_coimage_image_comparison C S C1 t T T0 P Q))
  walking_arrow_tgt) (@one_cat_kernel_family_projection_reflect_path (Functor_cat WalkingArrow_cat C) C S C1 t T T0 P
  (@diagram_evaluation_at_func WalkingArrow_cat C walking_arrow_src) (@cokernel_adjunction_arrow_func C S t T0 Q)
  (@sym_transf_tapp0_transf (Functor_cat WalkingArrow_cat C) WalkingArrow_cat C (@kernel_adjunction_arrow_func C S t T
  P) (@comp_cat_fapp0 (Functor_cat WalkingArrow_cat C) C (Functor_cat WalkingArrow_cat C) (@initial_arrow_diagram_func
  C t T0) (@fapp0 (Functor_cat (Functor_cat WalkingArrow_cat C) (Functor_cat WalkingArrow_cat C)) (Functor_cat
  (Functor_cat WalkingArrow_cat C) C) (@comp_cat_cov_func (Functor_cat WalkingArrow_cat C) (Functor_cat
  WalkingArrow_cat C) C (@kernel_adjunction_func C S t T P)) (@cokernel_adjunction_arrow_func C S t T0 Q))) (@fapp0 _
  _ (@one_cat_adjunction_family_transpose_func (Functor_cat WalkingArrow_cat C) (Functor_cat WalkingArrow_cat C) C
  (@one_cat_functor_category WalkingArrow_cat C C1) C1 (@cokernel_adjunction_func C S t T0 Q)
  (@initial_arrow_diagram_func C t T0) (@cokernel_adjunction_evidence C S t T0 Q) (@kernel_adjunction_arrow_func C S t
  T P) (@fapp0 (Functor_cat (Functor_cat WalkingArrow_cat C) (Functor_cat WalkingArrow_cat C)) (Functor_cat
  (Functor_cat WalkingArrow_cat C) C) (@comp_cat_cov_func (Functor_cat WalkingArrow_cat C) (Functor_cat
  WalkingArrow_cat C) C (@kernel_adjunction_func C S t T P)) (@cokernel_adjunction_arrow_func C S t T0 Q))) b)
  walking_arrow_tgt) (@one_cat_adjunction_source_to_image C S C1 t T T0 P Q)
      (@eq_trans (@Transf (Functor_cat WalkingArrow_cat C) C (@diagram_evaluation_at_func WalkingArrow_cat C
        walking_arrow_src) (@diagram_evaluation_at_func WalkingArrow_cat C walking_arrow_tgt))
        (@one_cat_coimage_image_factorization_value C S C1 t T T0 P Q b) (@diagram_evaluation_transf WalkingArrow_cat
        C walking_arrow_src walking_arrow_tgt walking_arrow_generator) (@sym_transf_tapp0_transf (Functor_cat
        WalkingArrow_cat C) WalkingArrow_cat C (@comp_cat_fapp0 (Functor_cat WalkingArrow_cat C) C (Functor_cat
        WalkingArrow_cat C) (@terminal_arrow_diagram_func C t T) (@diagram_evaluation_at_func WalkingArrow_cat C
        walking_arrow_src)) (@cokernel_adjunction_arrow_func C S t T0 Q) (@fapp0 _ _
        (@one_cat_adjunction_family_untranspose_func (Functor_cat WalkingArrow_cat C) C (Functor_cat WalkingArrow_cat
        C) C1 (@one_cat_functor_category WalkingArrow_cat C C1) (@terminal_arrow_diagram_func C t T)
        (@kernel_adjunction_func C S t T P) (@kernel_adjunction_evidence C S t T P) (@diagram_evaluation_at_func
        WalkingArrow_cat C walking_arrow_src) (@cokernel_adjunction_arrow_func C S t T0 Q))
        (@one_cat_adjunction_source_to_image C S C1 t T T0 P Q)) walking_arrow_src) p (@eq_sym (@Transf (Functor_cat
        WalkingArrow_cat C) C (@diagram_evaluation_at_func WalkingArrow_cat C walking_arrow_src)
        (@diagram_evaluation_at_func WalkingArrow_cat C walking_arrow_tgt)) (@sym_transf_tapp0_transf (Functor_cat
        WalkingArrow_cat C) WalkingArrow_cat C (@comp_cat_fapp0 (Functor_cat WalkingArrow_cat C) C (Functor_cat
        WalkingArrow_cat C) (@terminal_arrow_diagram_func C t T) (@diagram_evaluation_at_func WalkingArrow_cat C
        walking_arrow_src)) (@cokernel_adjunction_arrow_func C S t T0 Q) (@fapp0 _ _
        (@one_cat_adjunction_family_untranspose_func (Functor_cat WalkingArrow_cat C) C (Functor_cat WalkingArrow_cat
        C) C1 (@one_cat_functor_category WalkingArrow_cat C C1) (@terminal_arrow_diagram_func C t T)
        (@kernel_adjunction_func C S t T P) (@kernel_adjunction_evidence C S t T P) (@diagram_evaluation_at_func
        WalkingArrow_cat C walking_arrow_src) (@cokernel_adjunction_arrow_func C S t T0 Q))
        (@one_cat_adjunction_source_to_image C S C1 t T T0 P Q)) walking_arrow_src) (@diagram_evaluation_transf
        WalkingArrow_cat C walking_arrow_src walking_arrow_tgt walking_arrow_generator)
        (@one_cat_source_to_image_projection_path C S C1 t T T0 P Q)))) (@eq_sym (@Transf (Functor_cat
        WalkingArrow_cat C) C (@diagram_evaluation_at_func WalkingArrow_cat C walking_arrow_src) (@fapp0 (Functor_cat
        (Functor_cat WalkingArrow_cat C) (Functor_cat WalkingArrow_cat C)) (Functor_cat (Functor_cat WalkingArrow_cat
        C) C) (@comp_cat_cov_func (Functor_cat WalkingArrow_cat C) (Functor_cat WalkingArrow_cat C) C
        (@kernel_adjunction_func C S t T P)) (@cokernel_adjunction_arrow_func C S t T0 Q))) (@sym_transf_tapp0_transf
        (Functor_cat WalkingArrow_cat C) WalkingArrow_cat C (@kernel_adjunction_arrow_func C S t T P) (@comp_cat_fapp0
        (Functor_cat WalkingArrow_cat C) C (Functor_cat WalkingArrow_cat C) (@initial_arrow_diagram_func C t T0)
        (@fapp0 (Functor_cat (Functor_cat WalkingArrow_cat C) (Functor_cat WalkingArrow_cat C)) (Functor_cat
        (Functor_cat WalkingArrow_cat C) C) (@comp_cat_cov_func (Functor_cat WalkingArrow_cat C) (Functor_cat
        WalkingArrow_cat C) C (@kernel_adjunction_func C S t T P)) (@cokernel_adjunction_arrow_func C S t T0 Q)))
        (@fapp0 _ _ (@one_cat_adjunction_family_transpose_func (Functor_cat WalkingArrow_cat C) (Functor_cat
        WalkingArrow_cat C) C (@one_cat_functor_category WalkingArrow_cat C C1) C1 (@cokernel_adjunction_func C S t T0
        Q) (@initial_arrow_diagram_func C t T0) (@cokernel_adjunction_evidence C S t T0 Q)
        (@kernel_adjunction_arrow_func C S t T P) (@fapp0 (Functor_cat (Functor_cat WalkingArrow_cat C) (Functor_cat
        WalkingArrow_cat C)) (Functor_cat (Functor_cat WalkingArrow_cat C) C) (@comp_cat_cov_func (Functor_cat
        WalkingArrow_cat C) (Functor_cat WalkingArrow_cat C) C (@kernel_adjunction_func C S t T P))
        (@cokernel_adjunction_arrow_func C S t T0 Q))) (@one_cat_coimage_image_comparison C S C1 t T T0 P Q))
        walking_arrow_tgt) (@one_cat_adjunction_source_to_image C S C1 t T T0 P Q)
        (@one_cat_coimage_image_input_target_path C S C1 t T T0 P Q)));
