/* Whole H on the existing native zero-arrow-cone category. The ordinary
   target profile is explicit; neither input formation nor this operation
   requires selected per-arrow universal records. */
require open emdash.emdash3_2_one_cat_zero_cones;
require open emdash.emdash3_2_homology_adjunction_families;

symbol zero_arrow_cone_adjunction_homology_func [C : Cat] [S : τ (@PreadditiveCategory C)]
  (C1 : τ (IsNCat (cat_succ cat_zero) C))
  [t : τ (Obj C)] [T : τ (@TerminalObject C t)] [T0 : τ (@TerminalObject (Op_cat C) t)]
  (P : τ (@KernelAdjunctionStructure C S t T)) (Q : τ (@CokernelAdjunctionStructure C S t T0))
  : τ (Functor (@ZeroArrowCone_cat C t T) C)
≔ @homology_adjunction_family_func (@ZeroArrowCone_cat C t T) C S t T T0 P Q
    (@zero_arrow_cone_first_func C t T) (@zero_arrow_cone_diagram_func C t T)
    (@zero_arrow_cone_universal_transf C C1 t T);
