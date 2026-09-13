/* Native comparisons at the actual retained zero-end columns. */
require open emdash.emdash3_2_one_cat_terminal_family_universality;
require open emdash.emdash3_2_one_cat_kernel_cokernel_transposes;

// Original zero column, compared to its canonical embedding with fixed endpoints.
symbol one_cat_kernel_counit_zero_column_iso [C : Cat] [S : τ (@PreadditiveCategory C)]
  (C1 : τ (IsNCat (cat_succ cat_zero) C))
  [t : τ (Obj C)] [T : τ (@TerminalObject C t)]
  [T0 : τ (@TerminalObject (Op_cat C) t)]
  (P : τ (@KernelAdjunctionStructure C S t T))
  : τ (@DefIso (Functor_cat (Functor_cat WalkingArrow_cat C) (Functor_cat WalkingArrow_cat C)) (@one_cat_kernel_counit_zero_column_func C S C1 t T P) (@comp_cat_fapp0 (Functor_cat WalkingArrow_cat C) C (Functor_cat WalkingArrow_cat C) (@initial_arrow_diagram_func C t T0) (@diagram_evaluation_at_func WalkingArrow_cat C walking_arrow_tgt)))
≔ @one_cat_initial_arrow_family_iso (Functor_cat WalkingArrow_cat C) C C1 t T0 (@diagram_evaluation_at_func WalkingArrow_cat C walking_arrow_tgt)
    (@diagram_family_transf (Functor_cat WalkingArrow_cat C) WalkingArrow_cat C (@one_cat_kernel_counit_zero_column_func C S C1 t T P)
      walking_arrow_src walking_arrow_tgt walking_arrow_generator);

// The original transposed counit, composed with that universal comparison.
symbol one_cat_kernel_counit_mate_input [C : Cat] [S : τ (@PreadditiveCategory C)]
  (C1 : τ (IsNCat (cat_succ cat_zero) C))
  [t : τ (Obj C)] [T : τ (@TerminalObject C t)]
  [T0 : τ (@TerminalObject (Op_cat C) t)]
  (P : τ (@KernelAdjunctionStructure C S t T))
  : τ (@Transf (Functor_cat WalkingArrow_cat C) (Functor_cat WalkingArrow_cat C) (@kernel_adjunction_arrow_func C S t T P) (@comp_cat_fapp0 (Functor_cat WalkingArrow_cat C) C (Functor_cat WalkingArrow_cat C) (@initial_arrow_diagram_func C t T0) (@diagram_evaluation_at_func WalkingArrow_cat C walking_arrow_tgt)))
≔ @comp_fapp0 (Functor_cat (Functor_cat WalkingArrow_cat C) (Functor_cat WalkingArrow_cat C)) (@kernel_adjunction_arrow_func C S t T P) (@one_cat_kernel_counit_zero_column_func C S C1 t T P) (@comp_cat_fapp0 (Functor_cat WalkingArrow_cat C) C (Functor_cat WalkingArrow_cat C) (@initial_arrow_diagram_func C t T0) (@diagram_evaluation_at_func WalkingArrow_cat C walking_arrow_tgt))
    (@defiso_to _ _ _ (@one_cat_kernel_counit_zero_column_iso C S C1 t T T0 P)) (@one_cat_kernel_counit_transpose C S C1 t T P);

// Original zero column, compared to its canonical embedding with fixed endpoints.
symbol one_cat_cokernel_unit_zero_column_iso [C : Cat] [S : τ (@PreadditiveCategory C)]
  (C1 : τ (IsNCat (cat_succ cat_zero) C))
  [t : τ (Obj C)] [T : τ (@TerminalObject C t)]
  [T0 : τ (@TerminalObject (Op_cat C) t)]
  (Q : τ (@CokernelAdjunctionStructure C S t T0))
  : τ (@DefIso (Functor_cat (Functor_cat WalkingArrow_cat C) (Functor_cat WalkingArrow_cat C)) (@one_cat_cokernel_unit_zero_column_func C S C1 t T0 Q) (@comp_cat_fapp0 (Functor_cat WalkingArrow_cat C) C (Functor_cat WalkingArrow_cat C) (@terminal_arrow_diagram_func C t T) (@diagram_evaluation_at_func WalkingArrow_cat C walking_arrow_src)))
≔ @one_cat_terminal_arrow_family_iso (Functor_cat WalkingArrow_cat C) C C1 t T (@diagram_evaluation_at_func WalkingArrow_cat C walking_arrow_src)
    (@diagram_family_transf (Functor_cat WalkingArrow_cat C) WalkingArrow_cat C (@one_cat_cokernel_unit_zero_column_func C S C1 t T0 Q)
      walking_arrow_src walking_arrow_tgt walking_arrow_generator);

// The original transposed unit, composed with that universal comparison.
symbol one_cat_cokernel_unit_mate_input [C : Cat] [S : τ (@PreadditiveCategory C)]
  (C1 : τ (IsNCat (cat_succ cat_zero) C))
  [t : τ (Obj C)] [T : τ (@TerminalObject C t)]
  [T0 : τ (@TerminalObject (Op_cat C) t)]
  (Q : τ (@CokernelAdjunctionStructure C S t T0))
  : τ (@Transf (Functor_cat WalkingArrow_cat C) (Functor_cat WalkingArrow_cat C) (@comp_cat_fapp0 (Functor_cat WalkingArrow_cat C) C (Functor_cat WalkingArrow_cat C) (@terminal_arrow_diagram_func C t T) (@diagram_evaluation_at_func WalkingArrow_cat C walking_arrow_src)) (@cokernel_adjunction_arrow_func C S t T0 Q))
≔ @comp_fapp0 (Functor_cat (Functor_cat WalkingArrow_cat C) (Functor_cat WalkingArrow_cat C)) (@comp_cat_fapp0 (Functor_cat WalkingArrow_cat C) C (Functor_cat WalkingArrow_cat C) (@terminal_arrow_diagram_func C t T) (@diagram_evaluation_at_func WalkingArrow_cat C walking_arrow_src)) (@one_cat_cokernel_unit_zero_column_func C S C1 t T0 Q) (@cokernel_adjunction_arrow_func C S t T0 Q)
    (@one_cat_cokernel_unit_transpose C S C1 t T0 Q) (@defiso_from _ _ _ (@one_cat_cokernel_unit_zero_column_iso C S C1 t T T0 Q));
