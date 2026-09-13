/* Transpose the actual kernel counit and cokernel unit.
   The remaining zero-end columns are retained as whole functors. Relating
   them to the canonical zero-arrow embeddings is separate universal work. */
require open emdash.emdash3_2_one_cat_diagram_transpose;
require open emdash.emdash3_2_image_coimage_adjunction_families;

// The target column has source zero.
symbol one_cat_kernel_counit_zero_column_func [C : Cat] [S : τ (@PreadditiveCategory C)]
  (C1 : τ (IsNCat (cat_succ cat_zero) C))
  [t : τ (Obj C)] [T : τ (@TerminalObject C t)]
  (P : τ (@KernelAdjunctionStructure C S t T))
  : τ (Functor (Functor_cat WalkingArrow_cat C) (Functor_cat WalkingArrow_cat C))
≔ @one_cat_diagram_transpose_column_func (Functor_cat WalkingArrow_cat C) WalkingArrow_cat C C1
    (@comp_cat_fapp0 (Functor_cat WalkingArrow_cat C) C (Functor_cat WalkingArrow_cat C) (@terminal_arrow_diagram_func C t T) (@kernel_adjunction_func C S t T P)) (@id_func (Functor_cat WalkingArrow_cat C)) (@counit_adj_transf C (Functor_cat WalkingArrow_cat C) (@terminal_arrow_diagram_func C t T) (@kernel_adjunction_func C S t T P)
      (@kernel_adjunction_evidence C S t T P)) walking_arrow_tgt;

// The original counit, transposed at its actual kernel arrow.
symbol one_cat_kernel_counit_transpose [C : Cat] [S : τ (@PreadditiveCategory C)]
  (C1 : τ (IsNCat (cat_succ cat_zero) C))
  [t : τ (Obj C)] [T : τ (@TerminalObject C t)]
  (P : τ (@KernelAdjunctionStructure C S t T))
  : τ (@Transf (Functor_cat WalkingArrow_cat C) (Functor_cat WalkingArrow_cat C) (@kernel_adjunction_arrow_func C S t T P) (@one_cat_kernel_counit_zero_column_func C S C1 t T P))
≔ @one_cat_diagram_transpose_transf (Functor_cat WalkingArrow_cat C) WalkingArrow_cat C C1
    (@comp_cat_fapp0 (Functor_cat WalkingArrow_cat C) C (Functor_cat WalkingArrow_cat C) (@terminal_arrow_diagram_func C t T) (@kernel_adjunction_func C S t T P)) (@id_func (Functor_cat WalkingArrow_cat C)) (@counit_adj_transf C (Functor_cat WalkingArrow_cat C) (@terminal_arrow_diagram_func C t T) (@kernel_adjunction_func C S t T P)
      (@kernel_adjunction_evidence C S t T P))
    walking_arrow_src walking_arrow_tgt walking_arrow_generator;

// The source column has target zero.
symbol one_cat_cokernel_unit_zero_column_func [C : Cat] [S : τ (@PreadditiveCategory C)]
  (C1 : τ (IsNCat (cat_succ cat_zero) C))
  [t : τ (Obj C)] [T0 : τ (@TerminalObject (Op_cat C) t)]
  (Q : τ (@CokernelAdjunctionStructure C S t T0))
  : τ (Functor (Functor_cat WalkingArrow_cat C) (Functor_cat WalkingArrow_cat C))
≔ @one_cat_diagram_transpose_column_func (Functor_cat WalkingArrow_cat C) WalkingArrow_cat C C1
    (@id_func (Functor_cat WalkingArrow_cat C)) (@comp_cat_fapp0 (Functor_cat WalkingArrow_cat C) C (Functor_cat WalkingArrow_cat C) (@initial_arrow_diagram_func C t T0) (@cokernel_adjunction_func C S t T0 Q)) (@unit_adj_transf (Functor_cat WalkingArrow_cat C) C (@cokernel_adjunction_func C S t T0 Q) (@initial_arrow_diagram_func C t T0)
      (@cokernel_adjunction_evidence C S t T0 Q)) walking_arrow_src;

// The original unit, transposed at its actual cokernel arrow.
symbol one_cat_cokernel_unit_transpose [C : Cat] [S : τ (@PreadditiveCategory C)]
  (C1 : τ (IsNCat (cat_succ cat_zero) C))
  [t : τ (Obj C)] [T0 : τ (@TerminalObject (Op_cat C) t)]
  (Q : τ (@CokernelAdjunctionStructure C S t T0))
  : τ (@Transf (Functor_cat WalkingArrow_cat C) (Functor_cat WalkingArrow_cat C) (@one_cat_cokernel_unit_zero_column_func C S C1 t T0 Q) (@cokernel_adjunction_arrow_func C S t T0 Q))
≔ @one_cat_diagram_transpose_transf (Functor_cat WalkingArrow_cat C) WalkingArrow_cat C C1
    (@id_func (Functor_cat WalkingArrow_cat C)) (@comp_cat_fapp0 (Functor_cat WalkingArrow_cat C) C (Functor_cat WalkingArrow_cat C) (@initial_arrow_diagram_func C t T0) (@cokernel_adjunction_func C S t T0 Q)) (@unit_adj_transf (Functor_cat WalkingArrow_cat C) C (@cokernel_adjunction_func C S t T0 Q) (@initial_arrow_diagram_func C t T0)
      (@cokernel_adjunction_evidence C S t T0 Q))
    walking_arrow_src walking_arrow_tgt walking_arrow_generator;
