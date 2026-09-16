/* Optional ordinary factor-space view of the native boundary observation.
   Native data lives upstream; this owner only packages its original arrow
   and reconstruction as a factor-space point. No universal object is selected. */
require open emdash.emdash3_2_homology_adjunction_input_data;
require open emdash.emdash3_2_zero_arrow_universal_tests;

// Existing factor-space view with the actual semantic boundary as centre.
symbol kernel_adjunction_semantic_boundary_factor [C : Cat] [S : τ (@PreadditiveCategory C)]
  [t : τ (Obj C)] [T : τ (@TerminalObject C t)]
  (P : τ (@KernelAdjunctionStructure C S t T))
  (X : τ (Obj C)) (d : τ (Functor WalkingArrow_cat C))
  (h : τ (@Transf WalkingArrow_cat C
    (@fapp0 C (Functor_cat WalkingArrow_cat C) (@terminal_arrow_diagram_func C t T) X) d))
  : τ (@KernelFactorSpace C S (@fapp0 WalkingArrow_cat C d walking_arrow_src) (@fapp0 WalkingArrow_cat C d walking_arrow_tgt)
      (@terminal_arrow_test_outgoing C d) (@fapp0 _ _ (@kernel_adjunction_func C S t T P) d) (@tapp0_fapp0 _ _ _ _ d (@kernel_adjunction_inclusion C S t T P)) X
      (@terminal_arrow_kernel_test C S t T X d h))
≔ @Struct_sigma (Hom C X (@fapp0 _ _ (@kernel_adjunction_func C S t T P) d))
    (λ f : τ (Hom C X (@fapp0 _ _ (@kernel_adjunction_func C S t T P) d)), @= (Hom C X (@fapp0 WalkingArrow_cat C d walking_arrow_src))
      (@comp_fapp0 C X (@fapp0 _ _ (@kernel_adjunction_func C S t T P) d) (@fapp0 WalkingArrow_cat C d walking_arrow_src) (@tapp0_fapp0 _ _ _ _ d (@kernel_adjunction_inclusion C S t T P)) f)
      (@terminal_arrow_test_incoming C t T X d h))
    (@kernel_adjunction_semantic_boundary C S t T P X d h)
    (@kernel_adjunction_semantic_boundary_reconstruction C S t T P X d h);
