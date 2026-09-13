/* Whole homology on the native zero-cone category in an ordinary target.
   C1 is a local target profile, not a truncation of arbitrary source data. */
require open emdash.emdash3_2_zero_arrow_cone_adjunction_homology;
require open emdash.emdash3_2_homology_family_selected_views;

// Global H on the native cone category, via the already qualified family H.
symbol zero_arrow_cone_homology_func [C : Cat] [S : τ (@PreadditiveCategory C)]
  (C1 : τ (IsNCat (cat_succ cat_zero) C))
  [t : τ (Obj C)] [T : τ (@TerminalObject C t)] [T0 : τ (@TerminalObject (Op_cat C) t)]
  [W : τ (@HasComputationalKernels C S)] [V : τ (@HasComputationalCokernels C S)]
  (P : τ (@KernelPresentation C S t T W)) (Q : τ (@CokernelPresentation C S t T0 V))
  : τ (Functor (@ZeroArrowCone_cat C t T) C)
≔ @zero_arrow_cone_adjunction_homology_func C S C1 t T T0
    (@kernel_presentation_structure C S t T W P)
    (@cokernel_presentation_structure C S t T0 V Q);

/* Selected-object compatibility for the GLOBAL native zero-cone H. */

symbol zero_arrow_cone_homology_object_path [C : Cat] [S : τ (@PreadditiveCategory C)]
  (C1 : τ (IsNCat (cat_succ cat_zero) C))
  [t : τ (Obj C)] [T : τ (@TerminalObject C t)] [T0 : τ (@TerminalObject (Op_cat C) t)]
  [W : τ (@HasComputationalKernels C S)] [V : τ (@HasComputationalCokernels C S)]
  (P : τ (@KernelPresentation C S t T W)) (Q : τ (@CokernelPresentation C S t T0 V)) (z : τ (Obj (@ZeroArrowCone_cat C t T)))
  : τ (@= (Obj C) (@fapp0 (@ZeroArrowCone_cat C t T) C (@zero_arrow_cone_homology_func C S C1 t T T0 W V P Q) z)
      (@homology_family_selected_object (@ZeroArrowCone_cat C t T) C S t T W V (@zero_arrow_cone_first_func C t T) (@zero_arrow_cone_diagram_func C t T) (@zero_arrow_cone_universal_transf C C1 t T) z))
≔ @homology_family_object_path (@ZeroArrowCone_cat C t T) C S t T T0 W V P Q (@zero_arrow_cone_first_func C t T) (@zero_arrow_cone_diagram_func C t T) (@zero_arrow_cone_universal_transf C C1 t T) z;
