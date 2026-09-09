require open emdash.emdash3_2_kernel_adjunction_unmates;
require open emdash.emdash3_2_zero_arrow_cones;
require open emdash.emdash3_2_computational_homology;

/* Existing chain data enters the native category through an inverse mate.
   The original selected boundary is reused; no square or new choice is input. */

symbol chain_pair_outgoing_diagram [C : Cat] [S : τ (@PreadditiveCategory C)]
  [A B D : τ (Obj C)] (pair : τ (@ComputationalChainPair C S A B D))
  : τ (Functor WalkingArrow_cat C)
≔ @walking_arrow_func C B D (@computational_chain_pair_d C S A B D pair);

symbol chain_pair_selected_boundary [C : Cat] [S : τ (@PreadditiveCategory C)]
  (W : τ (@HasComputationalKernels C S)) [A B D : τ (Obj C)]
  (pair : τ (@ComputationalChainPair C S A B D))
  : τ (Hom C A (@kernel_presentation_selected_object C S W (@chain_pair_outgoing_diagram C S A B D pair)))
≔ @kernel_presentation_test_lift C S W A (@chain_pair_outgoing_diagram C S A B D pair)
    (@computational_chain_pair_cone C S A B D pair);

symbol chain_pair_zero_cone [C : Cat] [S : τ (@PreadditiveCategory C)] [t : τ (Obj C)]
  [T : τ (@TerminalObject C t)] [W : τ (@HasComputationalKernels C S)]
  (P : τ (@KernelPresentation C S t T W))
  [A B D : τ (Obj C)] (pair : τ (@ComputationalChainPair C S A B D))
  : τ (Obj (@ZeroArrowCone_cat C t T))
≔ @zero_arrow_cone_obj C t T A (@chain_pair_outgoing_diagram C S A B D pair) (@fapp0 _ _ (@kernel_presentation_unlift_func C S t T W P A (@chain_pair_outgoing_diagram C S A B D pair)) (@chain_pair_selected_boundary C S W A B D pair));
