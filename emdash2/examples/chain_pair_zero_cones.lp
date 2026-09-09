/* Original-selection and runtime native-entry computations. */
require open emdash.emdash3_2_chain_pair_zero_cones;

/* Check the selection input before expanding the contractible lift. */
assert [C : Cat] [S : τ (@PreadditiveCategory C)] [t : τ (Obj C)]
  [T : τ (@TerminalObject C t)] [W : τ (@HasComputationalKernels C S)]
  (P : τ (@KernelPresentation C S t T W))
  [A B D : τ (Obj C)] (pair : τ (@ComputationalChainPair C S A B D)) ⊢
  @kernel_presentation_selected C S W (@chain_pair_outgoing_diagram C S A B D pair)
  ≡ W B D (@computational_chain_pair_d C S A B D pair);
assert [C : Cat] [S : τ (@PreadditiveCategory C)] [t : τ (Obj C)]
  [T : τ (@TerminalObject C t)] [W : τ (@HasComputationalKernels C S)]
  (P : τ (@KernelPresentation C S t T W))
  [A B D : τ (Obj C)] (pair : τ (@ComputationalChainPair C S A B D)) ⊢
  @kernel_presentation_selected_object C S W (@chain_pair_outgoing_diagram C S A B D pair)
  ≡ @computational_kernel_object C S B D
      (@computational_chain_pair_d C S A B D pair)
      (W B D (@computational_chain_pair_d C S A B D pair));

assert [C : Cat] [S : τ (@PreadditiveCategory C)] [t : τ (Obj C)]
  [T : τ (@TerminalObject C t)] [W : τ (@HasComputationalKernels C S)]
  (P : τ (@KernelPresentation C S t T W))
  [A B D : τ (Obj C)] (pair : τ (@ComputationalChainPair C S A B D)) ⊢
  @fapp0 WalkingArrow_cat C (@chain_pair_outgoing_diagram C S A B D pair) walking_arrow_src ≡ B;

assert [C : Cat] [S : τ (@PreadditiveCategory C)] [t : τ (Obj C)]
  [T : τ (@TerminalObject C t)] [W : τ (@HasComputationalKernels C S)]
  (P : τ (@KernelPresentation C S t T W))
  [A B D : τ (Obj C)] (pair : τ (@ComputationalChainPair C S A B D)) ⊢
  @fapp0 WalkingArrow_cat C (@chain_pair_outgoing_diagram C S A B D pair) walking_arrow_tgt ≡ D;

assert [C : Cat] [S : τ (@PreadditiveCategory C)] [t : τ (Obj C)]
  [T : τ (@TerminalObject C t)] [W : τ (@HasComputationalKernels C S)]
  (P : τ (@KernelPresentation C S t T W))
  [A B D : τ (Obj C)] (pair : τ (@ComputationalChainPair C S A B D)) ⊢
  @fapp1_fapp0 WalkingArrow_cat C (@chain_pair_outgoing_diagram C S A B D pair)
    walking_arrow_src walking_arrow_tgt walking_arrow_generator
  ≡ @computational_chain_pair_d C S A B D pair;

assert [C : Cat] [S : τ (@PreadditiveCategory C)] [t : τ (Obj C)]
  [T : τ (@TerminalObject C t)] [W : τ (@HasComputationalKernels C S)]
  (P : τ (@KernelPresentation C S t T W))
  [A B D : τ (Obj C)] (pair : τ (@ComputationalChainPair C S A B D)) ⊢
  @fapp0 (@ZeroArrowCone_cat C t T) C (@zero_arrow_cone_first_func C t T) (@chain_pair_zero_cone C S t T W P A B D pair) ≡ A;

assert [C : Cat] [S : τ (@PreadditiveCategory C)] [t : τ (Obj C)]
  [T : τ (@TerminalObject C t)] [W : τ (@HasComputationalKernels C S)]
  (P : τ (@KernelPresentation C S t T W))
  [A B D : τ (Obj C)] (pair : τ (@ComputationalChainPair C S A B D)) ⊢
  @fapp0 (@ZeroArrowCone_cat C t T) (Functor_cat WalkingArrow_cat C)
    (@zero_arrow_cone_diagram_func C t T) (@chain_pair_zero_cone C S t T W P A B D pair) ≡ (@chain_pair_outgoing_diagram C S A B D pair);

assert [C : Cat] [S : τ (@PreadditiveCategory C)] [t : τ (Obj C)]
  [T : τ (@TerminalObject C t)] [W : τ (@HasComputationalKernels C S)]
  (P : τ (@KernelPresentation C S t T W))
  [A B D : τ (Obj C)] (pair : τ (@ComputationalChainPair C S A B D)) ⊢
  @fapp0 _ _ (@kernel_presentation_lift_func C S t T W P A (@chain_pair_outgoing_diagram C S A B D pair))
    (@fapp0 _ _ (@kernel_presentation_unlift_func C S t T W P A (@chain_pair_outgoing_diagram C S A B D pair)) (@chain_pair_selected_boundary C S W A B D pair))
  ≡ (@chain_pair_selected_boundary C S W A B D pair);

// Native entry does not identify an unrelated selected lift.
assertnot [C : Cat] [S : τ (@PreadditiveCategory C)] [t : τ (Obj C)]
  [T : τ (@TerminalObject C t)] [W : τ (@HasComputationalKernels C S)]
  (P : τ (@KernelPresentation C S t T W))
  [A B D : τ (Obj C)] (pair : τ (@ComputationalChainPair C S A B D)) (other : τ (Hom C A (@kernel_presentation_selected_object C S W (@chain_pair_outgoing_diagram C S A B D pair)))) ⊢
  eq_refl (@chain_pair_selected_boundary C S W A B D pair) : τ (@= (Hom C A (@kernel_presentation_selected_object C S W (@chain_pair_outgoing_diagram C S A B D pair))) (@chain_pair_selected_boundary C S W A B D pair) other);
