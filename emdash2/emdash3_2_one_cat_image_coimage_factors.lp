/* Two canonical whole factors, using native zero-column comparisons and mates. */
require open emdash.emdash3_2_one_cat_adjunction_zero_columns;
require open emdash.emdash3_2_cokernel_adjunction_families;
require open emdash.emdash3_2_homology_adjunction_families;

// Coim(f)→cod(f), as the whole cokernel mate of the transposed counit.
symbol one_cat_adjunction_coimage_to_target
  [C : Cat] [S : τ (@PreadditiveCategory C)]
  (C1 : τ (IsNCat (cat_succ cat_zero) C))
  [t : τ (Obj C)] [T : τ (@TerminalObject C t)] [T0 : τ (@TerminalObject (Op_cat C) t)]
  (P : τ (@KernelAdjunctionStructure C S t T))
  (Q : τ (@CokernelAdjunctionStructure C S t T0))
  : τ (@Transf (Functor_cat WalkingArrow_cat C) C
      (@adjunction_coimage_func C S t T T0 P Q)
      (@diagram_evaluation_at_func WalkingArrow_cat C walking_arrow_tgt))
≔ @cokernel_adjunction_family_colift_transf (Functor_cat WalkingArrow_cat C) C S t T0 Q
    (@kernel_adjunction_arrow_func C S t T P)
    (@diagram_evaluation_at_func WalkingArrow_cat C walking_arrow_tgt)
    (@one_cat_kernel_counit_mate_input C S C1 t T T0 P);

// dom(f)→Im(f), as the whole kernel mate of the transposed unit.
symbol one_cat_adjunction_source_to_image
  [C : Cat] [S : τ (@PreadditiveCategory C)]
  (C1 : τ (IsNCat (cat_succ cat_zero) C))
  [t : τ (Obj C)] [T : τ (@TerminalObject C t)] [T0 : τ (@TerminalObject (Op_cat C) t)]
  (P : τ (@KernelAdjunctionStructure C S t T))
  (Q : τ (@CokernelAdjunctionStructure C S t T0))
  : τ (@Transf (Functor_cat WalkingArrow_cat C) C
      (@diagram_evaluation_at_func WalkingArrow_cat C walking_arrow_src)
      (@adjunction_image_func C S t T T0 P Q))
≔ @kernel_adjunction_family_boundary_transf (Functor_cat WalkingArrow_cat C) C S t T P
    (@diagram_evaluation_at_func WalkingArrow_cat C walking_arrow_src)
    (@cokernel_adjunction_arrow_func C S t T0 Q)
    (@one_cat_cokernel_unit_mate_input C S C1 t T T0 Q);
