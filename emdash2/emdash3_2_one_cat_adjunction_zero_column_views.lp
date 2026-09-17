/* Whole differential observations of the original normalized adjunction inputs.
   The composition proof is the generic functoriality observation of the
   whole family evaluator combined with the derived identity-endpoint laws.
   The original unit/counit transposes and their whole differential observations
   are retained. There is no additional caller square or ordinary record. */
require open emdash.emdash3_2_one_cat_adjunction_zero_column_observations;

// The normalized unit source is the original whole differential.
symbol one_cat_cokernel_unit_source_transf_path [C : Cat] [S : τ (@PreadditiveCategory C)]
  (C1 : τ (IsNCat (cat_succ cat_zero) C))
  [t : τ (Obj C)] [T : τ (@TerminalObject C t)] [T0 : τ (@TerminalObject (Op_cat C) t)]
  (Q : τ (@CokernelAdjunctionStructure C S t T0))
  : τ (@= (@Transf (Functor_cat WalkingArrow_cat C) C (@diagram_evaluation_at_func WalkingArrow_cat C walking_arrow_src)
    (@diagram_evaluation_at_func WalkingArrow_cat C walking_arrow_tgt))
      (@sym_transf_tapp0_transf (Functor_cat WalkingArrow_cat C) WalkingArrow_cat C (@comp_cat_fapp0 (Functor_cat
        WalkingArrow_cat C) C (Functor_cat WalkingArrow_cat C) (@terminal_arrow_diagram_func C t T)
        (@diagram_evaluation_at_func WalkingArrow_cat C walking_arrow_src)) (@cokernel_adjunction_arrow_func C S t T0 Q)
        (@one_cat_cokernel_unit_mate_input C S C1 t T T0 Q) walking_arrow_src)
      (@diagram_evaluation_transf WalkingArrow_cat C walking_arrow_src walking_arrow_tgt walking_arrow_generator))
≔ @eq_trans (@Transf (Functor_cat WalkingArrow_cat C) C (@diagram_evaluation_at_func WalkingArrow_cat C walking_arrow_src) (@diagram_evaluation_at_func WalkingArrow_cat C walking_arrow_tgt)) (@sym_transf_tapp0_transf (Functor_cat WalkingArrow_cat C) WalkingArrow_cat C (@comp_cat_fapp0 (Functor_cat
        WalkingArrow_cat C) C (Functor_cat WalkingArrow_cat C) (@terminal_arrow_diagram_func C t T)
        (@diagram_evaluation_at_func WalkingArrow_cat C walking_arrow_src)) (@cokernel_adjunction_arrow_func C S t T0 Q)
        (@one_cat_cokernel_unit_mate_input C S C1 t T T0 Q) walking_arrow_src) (@comp_fapp0 (Functor_cat (Functor_cat WalkingArrow_cat C) C) (@diagram_evaluation_at_func WalkingArrow_cat C walking_arrow_src) (@diagram_evaluation_at_func WalkingArrow_cat C walking_arrow_src) (@diagram_evaluation_at_func WalkingArrow_cat C walking_arrow_tgt) (@diagram_evaluation_transf WalkingArrow_cat C walking_arrow_src walking_arrow_tgt walking_arrow_generator) (@sym_transf_tapp0_transf (Functor_cat WalkingArrow_cat C) WalkingArrow_cat C (@comp_cat_fapp0 (Functor_cat WalkingArrow_cat C) C (Functor_cat WalkingArrow_cat C) (@terminal_arrow_diagram_func C t T) (@diagram_evaluation_at_func WalkingArrow_cat C walking_arrow_src)) (@one_cat_cokernel_unit_zero_column_func C S C1 t T0 Q) (@iso_evidence_from _ _ _ (@one_cat_cokernel_unit_zero_column_evidence C S C1 t T T0 Q)) walking_arrow_src)) (@diagram_evaluation_transf WalkingArrow_cat C walking_arrow_src walking_arrow_tgt walking_arrow_generator)
    (@one_cat_diagram_family_evaluation_comp_path (Functor_cat WalkingArrow_cat C) WalkingArrow_cat C C1 walking_arrow_src
  (@comp_cat_fapp0 (Functor_cat WalkingArrow_cat C) C (Functor_cat WalkingArrow_cat C) (@terminal_arrow_diagram_func C t
  T) (@diagram_evaluation_at_func WalkingArrow_cat C walking_arrow_src)) (@one_cat_cokernel_unit_zero_column_func C S C1
  t T0 Q) (@cokernel_adjunction_arrow_func C S t T0 Q) (@one_cat_cokernel_unit_transpose C S C1 t T0 Q) (@iso_evidence_from _
  _ _ (@one_cat_cokernel_unit_zero_column_evidence C S C1 t T T0 Q)))
    (@eq_ap (@Transf (Functor_cat WalkingArrow_cat C) C (@diagram_evaluation_at_func WalkingArrow_cat C walking_arrow_src) (@diagram_evaluation_at_func WalkingArrow_cat C walking_arrow_src)) (@Transf (Functor_cat WalkingArrow_cat C) C (@diagram_evaluation_at_func WalkingArrow_cat C walking_arrow_src) (@diagram_evaluation_at_func WalkingArrow_cat C walking_arrow_tgt)) (λ v : τ (@Transf (Functor_cat WalkingArrow_cat C) C (@diagram_evaluation_at_func WalkingArrow_cat C walking_arrow_src) (@diagram_evaluation_at_func WalkingArrow_cat C walking_arrow_src)), @comp_fapp0 (Functor_cat (Functor_cat WalkingArrow_cat C) C) (@diagram_evaluation_at_func WalkingArrow_cat C walking_arrow_src) (@diagram_evaluation_at_func WalkingArrow_cat C walking_arrow_src) (@diagram_evaluation_at_func WalkingArrow_cat C walking_arrow_tgt) (@diagram_evaluation_transf WalkingArrow_cat C walking_arrow_src walking_arrow_tgt walking_arrow_generator) v) (@sym_transf_tapp0_transf (Functor_cat WalkingArrow_cat C) WalkingArrow_cat C (@comp_cat_fapp0 (Functor_cat WalkingArrow_cat C) C (Functor_cat WalkingArrow_cat C) (@terminal_arrow_diagram_func C t T) (@diagram_evaluation_at_func WalkingArrow_cat C walking_arrow_src)) (@one_cat_cokernel_unit_zero_column_func C S C1 t T0 Q) (@iso_evidence_from _ _ _ (@one_cat_cokernel_unit_zero_column_evidence C S C1 t T T0 Q)) walking_arrow_src) (@id (Functor_cat (Functor_cat WalkingArrow_cat C) C) (@diagram_evaluation_at_func WalkingArrow_cat C walking_arrow_src)) (@one_cat_cokernel_unit_zero_column_from_src_path C S C1 t T T0 Q));

// The normalized counit target is the original whole differential.
symbol one_cat_kernel_counit_target_transf_path [C : Cat] [S : τ (@PreadditiveCategory C)]
  (C1 : τ (IsNCat (cat_succ cat_zero) C))
  [t : τ (Obj C)] [T : τ (@TerminalObject C t)] [T0 : τ (@TerminalObject (Op_cat C) t)]
  (P : τ (@KernelAdjunctionStructure C S t T))
  : τ (@= (@Transf (Functor_cat WalkingArrow_cat C) C (@diagram_evaluation_at_func WalkingArrow_cat C walking_arrow_src)
    (@diagram_evaluation_at_func WalkingArrow_cat C walking_arrow_tgt))
      (@sym_transf_tapp0_transf (Functor_cat WalkingArrow_cat C) WalkingArrow_cat C (@kernel_adjunction_arrow_func C S t
        T P) (@comp_cat_fapp0 (Functor_cat WalkingArrow_cat C) C (Functor_cat WalkingArrow_cat C)
        (@initial_arrow_diagram_func C t T0) (@diagram_evaluation_at_func WalkingArrow_cat C walking_arrow_tgt))
        (@one_cat_kernel_counit_mate_input C S C1 t T T0 P) walking_arrow_tgt)
      (@diagram_evaluation_transf WalkingArrow_cat C walking_arrow_src walking_arrow_tgt walking_arrow_generator))
≔ @eq_trans (@Transf (Functor_cat WalkingArrow_cat C) C (@diagram_evaluation_at_func WalkingArrow_cat C walking_arrow_src) (@diagram_evaluation_at_func WalkingArrow_cat C walking_arrow_tgt)) (@sym_transf_tapp0_transf (Functor_cat WalkingArrow_cat C) WalkingArrow_cat C (@kernel_adjunction_arrow_func C S t
        T P) (@comp_cat_fapp0 (Functor_cat WalkingArrow_cat C) C (Functor_cat WalkingArrow_cat C)
        (@initial_arrow_diagram_func C t T0) (@diagram_evaluation_at_func WalkingArrow_cat C walking_arrow_tgt))
        (@one_cat_kernel_counit_mate_input C S C1 t T T0 P) walking_arrow_tgt) (@comp_fapp0 (Functor_cat (Functor_cat WalkingArrow_cat C) C) (@diagram_evaluation_at_func WalkingArrow_cat C walking_arrow_src) (@diagram_evaluation_at_func WalkingArrow_cat C walking_arrow_tgt) (@diagram_evaluation_at_func WalkingArrow_cat C walking_arrow_tgt) (@sym_transf_tapp0_transf (Functor_cat WalkingArrow_cat C) WalkingArrow_cat C (@one_cat_kernel_counit_zero_column_func C S C1 t T P) (@comp_cat_fapp0 (Functor_cat WalkingArrow_cat C) C (Functor_cat WalkingArrow_cat C) (@initial_arrow_diagram_func C t T0) (@diagram_evaluation_at_func WalkingArrow_cat C walking_arrow_tgt)) (@iso_evidence_to _ _ _ (@one_cat_kernel_counit_zero_column_evidence C S C1 t T T0 P)) walking_arrow_tgt) (@diagram_evaluation_transf WalkingArrow_cat C walking_arrow_src walking_arrow_tgt walking_arrow_generator)) (@diagram_evaluation_transf WalkingArrow_cat C walking_arrow_src walking_arrow_tgt walking_arrow_generator)
    (@one_cat_diagram_family_evaluation_comp_path (Functor_cat WalkingArrow_cat C) WalkingArrow_cat C C1 walking_arrow_tgt
  (@kernel_adjunction_arrow_func C S t T P) (@one_cat_kernel_counit_zero_column_func C S C1 t T P) (@comp_cat_fapp0
  (Functor_cat WalkingArrow_cat C) C (Functor_cat WalkingArrow_cat C) (@initial_arrow_diagram_func C t T0)
  (@diagram_evaluation_at_func WalkingArrow_cat C walking_arrow_tgt)) (@iso_evidence_to _ _ _
  (@one_cat_kernel_counit_zero_column_evidence C S C1 t T T0 P)) (@one_cat_kernel_counit_transpose C S C1 t T P))
    (@eq_ap (@Transf (Functor_cat WalkingArrow_cat C) C (@diagram_evaluation_at_func WalkingArrow_cat C walking_arrow_tgt) (@diagram_evaluation_at_func WalkingArrow_cat C walking_arrow_tgt)) (@Transf (Functor_cat WalkingArrow_cat C) C (@diagram_evaluation_at_func WalkingArrow_cat C walking_arrow_src) (@diagram_evaluation_at_func WalkingArrow_cat C walking_arrow_tgt)) (λ v : τ (@Transf (Functor_cat WalkingArrow_cat C) C (@diagram_evaluation_at_func WalkingArrow_cat C walking_arrow_tgt) (@diagram_evaluation_at_func WalkingArrow_cat C walking_arrow_tgt)), @comp_fapp0 (Functor_cat (Functor_cat WalkingArrow_cat C) C) (@diagram_evaluation_at_func WalkingArrow_cat C walking_arrow_src) (@diagram_evaluation_at_func WalkingArrow_cat C walking_arrow_tgt) (@diagram_evaluation_at_func WalkingArrow_cat C walking_arrow_tgt) v (@diagram_evaluation_transf WalkingArrow_cat C walking_arrow_src walking_arrow_tgt walking_arrow_generator)) (@sym_transf_tapp0_transf (Functor_cat WalkingArrow_cat C) WalkingArrow_cat C (@one_cat_kernel_counit_zero_column_func C S C1 t T P) (@comp_cat_fapp0 (Functor_cat WalkingArrow_cat C) C (Functor_cat WalkingArrow_cat C) (@initial_arrow_diagram_func C t T0) (@diagram_evaluation_at_func WalkingArrow_cat C walking_arrow_tgt)) (@iso_evidence_to _ _ _ (@one_cat_kernel_counit_zero_column_evidence C S C1 t T T0 P)) walking_arrow_tgt) (@id (Functor_cat (Functor_cat WalkingArrow_cat C) C) (@diagram_evaluation_at_func WalkingArrow_cat C walking_arrow_tgt)) (@one_cat_kernel_counit_zero_column_to_tgt_path C S C1 t T T0 P));
