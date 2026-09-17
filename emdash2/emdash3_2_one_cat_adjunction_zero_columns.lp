/* Native zero-column comparisons derived from primary whole universality.
   The actual original column, map and inverse are retained. Ordinary inverse
   laws are proved; no output exactness or extra DefIso normalizer is assumed. */
require open emdash.emdash3_2_one_cat_terminal_adjunction_families;
require open emdash.emdash3_2_one_cat_terminal_adjunctions;
require open emdash.emdash3_2_one_cat_kernel_cokernel_transposes;

// Derived comparison at the actual native kernel zero column.
symbol one_cat_kernel_counit_zero_column_evidence [C : Cat] [S : τ (@PreadditiveCategory C)]
  (C1 : τ (IsNCat (cat_succ cat_zero) C))
  [t : τ (Obj C)] [T : τ (@TerminalObject C t)] [T0 : τ (@TerminalObject (Op_cat C) t)]
  (P : τ (@KernelAdjunctionStructure C S t T))
  : τ (IsoEvidence (Functor_cat (Functor_cat WalkingArrow_cat C) (Functor_cat WalkingArrow_cat C)) (@one_cat_kernel_counit_zero_column_func C S C1 t T P) (@comp_cat_fapp0 (Functor_cat WalkingArrow_cat C) C (Functor_cat WalkingArrow_cat C) (@initial_arrow_diagram_func C t T0) (@diagram_evaluation_at_func WalkingArrow_cat C walking_arrow_tgt)))
≔ @iso_evidence_comp (Functor_cat (Functor_cat WalkingArrow_cat C) (Functor_cat WalkingArrow_cat C)) _ _ _
    (@one_cat_initial_adjunction_family_presentation_evidence (Functor_cat WalkingArrow_cat C) C C1 t
      (@one_cat_initial_adjunction C C1 t T0) (@diagram_evaluation_at_func WalkingArrow_cat C walking_arrow_tgt)
      (@initial_arrow_transf C t T0) (@diagram_family_transf (Functor_cat WalkingArrow_cat C) WalkingArrow_cat C (@one_cat_kernel_counit_zero_column_func C S C1 t T P) walking_arrow_src walking_arrow_tgt walking_arrow_generator))
    (@iso_evidence_sym _ _ _ (@one_cat_diagram_family_reconstruction_evidence (Functor_cat WalkingArrow_cat C) C C1 (@one_cat_kernel_counit_zero_column_func C S C1 t T P)));

// Derived comparison at the actual native cokernel zero column.
symbol one_cat_cokernel_unit_zero_column_evidence [C : Cat] [S : τ (@PreadditiveCategory C)]
  (C1 : τ (IsNCat (cat_succ cat_zero) C))
  [t : τ (Obj C)] [T : τ (@TerminalObject C t)] [T0 : τ (@TerminalObject (Op_cat C) t)]
  (Q : τ (@CokernelAdjunctionStructure C S t T0))
  : τ (IsoEvidence (Functor_cat (Functor_cat WalkingArrow_cat C) (Functor_cat WalkingArrow_cat C)) (@one_cat_cokernel_unit_zero_column_func C S C1 t T0 Q) (@comp_cat_fapp0 (Functor_cat WalkingArrow_cat C) C (Functor_cat WalkingArrow_cat C) (@terminal_arrow_diagram_func C t T) (@diagram_evaluation_at_func WalkingArrow_cat C walking_arrow_src)))
≔ @iso_evidence_comp (Functor_cat (Functor_cat WalkingArrow_cat C) (Functor_cat WalkingArrow_cat C)) _ _ _
    (@one_cat_terminal_adjunction_family_presentation_evidence (Functor_cat WalkingArrow_cat C) C C1 t
      (@one_cat_terminal_adjunction C C1 t T) (@diagram_evaluation_at_func WalkingArrow_cat C walking_arrow_src)
      (@terminal_arrow_transf C t T) (@diagram_family_transf (Functor_cat WalkingArrow_cat C) WalkingArrow_cat C (@one_cat_cokernel_unit_zero_column_func C S C1 t T0 Q) walking_arrow_src walking_arrow_tgt walking_arrow_generator))
    (@iso_evidence_sym _ _ _ (@one_cat_diagram_family_reconstruction_evidence (Functor_cat WalkingArrow_cat C) C C1 (@one_cat_cokernel_unit_zero_column_func C S C1 t T0 Q)));

// Compose the original counit/unit transpose with the same derived comparison.
symbol one_cat_kernel_counit_mate_input [C : Cat] [S : τ (@PreadditiveCategory C)]
  (C1 : τ (IsNCat (cat_succ cat_zero) C))
  [t : τ (Obj C)] [T : τ (@TerminalObject C t)]
  [T0 : τ (@TerminalObject (Op_cat C) t)]
  (P : τ (@KernelAdjunctionStructure C S t T))
  : τ (@Transf (Functor_cat WalkingArrow_cat C) (Functor_cat WalkingArrow_cat C) (@kernel_adjunction_arrow_func C S t T P) (@comp_cat_fapp0 (Functor_cat WalkingArrow_cat C) C (Functor_cat WalkingArrow_cat C) (@initial_arrow_diagram_func C t T0) (@diagram_evaluation_at_func WalkingArrow_cat C walking_arrow_tgt)))
≔ @comp_fapp0 (Functor_cat (Functor_cat WalkingArrow_cat C) (Functor_cat WalkingArrow_cat C)) (@kernel_adjunction_arrow_func C S t T P) (@one_cat_kernel_counit_zero_column_func C S C1 t T P) (@comp_cat_fapp0 (Functor_cat WalkingArrow_cat C) C (Functor_cat WalkingArrow_cat C) (@initial_arrow_diagram_func C t T0) (@diagram_evaluation_at_func WalkingArrow_cat C walking_arrow_tgt))
    (@iso_evidence_to _ _ _ (@one_cat_kernel_counit_zero_column_evidence C S C1 t T T0 P)) (@one_cat_kernel_counit_transpose C S C1 t T P);

symbol one_cat_cokernel_unit_mate_input [C : Cat] [S : τ (@PreadditiveCategory C)]
  (C1 : τ (IsNCat (cat_succ cat_zero) C))
  [t : τ (Obj C)] [T : τ (@TerminalObject C t)]
  [T0 : τ (@TerminalObject (Op_cat C) t)]
  (Q : τ (@CokernelAdjunctionStructure C S t T0))
  : τ (@Transf (Functor_cat WalkingArrow_cat C) (Functor_cat WalkingArrow_cat C) (@comp_cat_fapp0 (Functor_cat WalkingArrow_cat C) C (Functor_cat WalkingArrow_cat C) (@terminal_arrow_diagram_func C t T) (@diagram_evaluation_at_func WalkingArrow_cat C walking_arrow_src)) (@cokernel_adjunction_arrow_func C S t T0 Q))
≔ @comp_fapp0 (Functor_cat (Functor_cat WalkingArrow_cat C) (Functor_cat WalkingArrow_cat C)) (@comp_cat_fapp0 (Functor_cat WalkingArrow_cat C) C (Functor_cat WalkingArrow_cat C) (@terminal_arrow_diagram_func C t T) (@diagram_evaluation_at_func WalkingArrow_cat C walking_arrow_src)) (@one_cat_cokernel_unit_zero_column_func C S C1 t T0 Q) (@cokernel_adjunction_arrow_func C S t T0 Q)
    (@one_cat_cokernel_unit_transpose C S C1 t T0 Q) (@iso_evidence_from _ _ _ (@one_cat_cokernel_unit_zero_column_evidence C S C1 t T T0 Q));
