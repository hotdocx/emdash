/* Whole forward/backward universal maps. The existing adjunction mate
   owners provide their computation and cancellation; no selected W/V data. */
require open emdash.emdash3_2_kernel_cokernel_adjunctions;
require open emdash.emdash3_2_adjunction_mates;

symbol kernel_adjunction_lift_func [C : Cat] [S : τ (@PreadditiveCategory C)]
  [t : τ (Obj C)] [T : τ (@TerminalObject C t)]
  (U : τ (@KernelAdjunctionStructure C S t T))
  (X : τ (Obj C)) (d : τ (Functor WalkingArrow_cat C))
  : τ (Functor (Hom_cat (Functor_cat WalkingArrow_cat C)
      (@fapp0 C (Functor_cat WalkingArrow_cat C) (@terminal_arrow_diagram_func C t T) X) d)
      (Hom_cat C X (@fapp0 (Functor_cat WalkingArrow_cat C) C (@kernel_adjunction_func C S t T U) d)))
≔ @adjunction_transpose_func C (Functor_cat WalkingArrow_cat C)
    (@terminal_arrow_diagram_func C t T) (@kernel_adjunction_func C S t T U) (@kernel_adjunction_evidence C S t T U) X d;

symbol kernel_adjunction_unlift_func [C : Cat] [S : τ (@PreadditiveCategory C)]
  [t : τ (Obj C)] [T : τ (@TerminalObject C t)]
  (U : τ (@KernelAdjunctionStructure C S t T))
  (X : τ (Obj C)) (d : τ (Functor WalkingArrow_cat C))
  : τ (Functor (Hom_cat C X (@fapp0 (Functor_cat WalkingArrow_cat C) C (@kernel_adjunction_func C S t T U) d))
      (Hom_cat (Functor_cat WalkingArrow_cat C)
      (@fapp0 C (Functor_cat WalkingArrow_cat C) (@terminal_arrow_diagram_func C t T) X) d))
≔ @adjunction_untranspose_func C (Functor_cat WalkingArrow_cat C)
    (@terminal_arrow_diagram_func C t T) (@kernel_adjunction_func C S t T U) (@kernel_adjunction_evidence C S t T U) X d;

symbol cokernel_adjunction_colift_func [C : Cat] [S : τ (@PreadditiveCategory C)]
  [t : τ (Obj C)] [T : τ (@TerminalObject (Op_cat C) t)]
  (U : τ (@CokernelAdjunctionStructure C S t T))
  (X : τ (Obj C)) (d : τ (Functor WalkingArrow_cat C))
  : τ (Functor (Hom_cat (Functor_cat WalkingArrow_cat C) d
      (@fapp0 C (Functor_cat WalkingArrow_cat C) (@initial_arrow_diagram_func C t T) X))
      (Hom_cat C (@fapp0 (Functor_cat WalkingArrow_cat C) C (@cokernel_adjunction_func C S t T U) d) X))
≔ @adjunction_untranspose_func (Functor_cat WalkingArrow_cat C) C
    (@cokernel_adjunction_func C S t T U) (@initial_arrow_diagram_func C t T) (@cokernel_adjunction_evidence C S t T U) d X;

symbol cokernel_adjunction_uncolift_func [C : Cat] [S : τ (@PreadditiveCategory C)]
  [t : τ (Obj C)] [T : τ (@TerminalObject (Op_cat C) t)]
  (U : τ (@CokernelAdjunctionStructure C S t T))
  (X : τ (Obj C)) (d : τ (Functor WalkingArrow_cat C))
  : τ (Functor (Hom_cat C (@fapp0 (Functor_cat WalkingArrow_cat C) C (@cokernel_adjunction_func C S t T U) d) X)
      (Hom_cat (Functor_cat WalkingArrow_cat C) d
      (@fapp0 C (Functor_cat WalkingArrow_cat C) (@initial_arrow_diagram_func C t T) X)))
≔ @adjunction_transpose_func (Functor_cat WalkingArrow_cat C) C
    (@cokernel_adjunction_func C S t T U) (@initial_arrow_diagram_func C t T) (@cokernel_adjunction_evidence C S t T U) d X;
