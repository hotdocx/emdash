require open emdash.emdash3_2_kernel_adjunction_mates;

/* Whole inverse kernel mate, transparently specialized from the adjunction.
   Reconstruction comparisons live in kernel_adjunction_unmate_paths. */

symbol kernel_presentation_unlift_func [C : Cat] [S : τ (@PreadditiveCategory C)] [t : τ (Obj C)]
  [T : τ (@TerminalObject C t)] [W : τ (@HasComputationalKernels C S)]
  (P : τ (@KernelPresentation C S t T W)) (X : τ (Obj C)) (d : τ (Functor WalkingArrow_cat C))
  : τ (Functor (Hom_cat C X (@fapp0 (Functor_cat WalkingArrow_cat C) C (@kernel_presentation_func C S t T W P) d)) (Hom_cat (Functor_cat WalkingArrow_cat C) (@fapp0 C (Functor_cat WalkingArrow_cat C) (@terminal_arrow_diagram_func C t T) X) d))
≔ (@adjunction_untranspose_func C (Functor_cat WalkingArrow_cat C) (@terminal_arrow_diagram_func C t T) (@kernel_presentation_func C S t T W P) (@kernel_presentation_adjunction C S t T W P) X d);
