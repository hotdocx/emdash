require open emdash.emdash3_2_chain_pair_zero_cone_comparisons;

// Same embedding/lift law is available through its named comparison.
assert [C : Cat] [S : τ (@PreadditiveCategory C)] [t : τ (Obj C)]
  [T : τ (@TerminalObject C t)] [W : τ (@HasComputationalKernels C S)]
  (P : τ (@KernelPresentation C S t T W))
  [A B D : τ (Obj C)] (pair : τ (@ComputationalChainPair C S A B D)) ⊢
  @chain_pair_zero_cone_incoming_path C S t T W P A B D pair
  : τ (@= (Hom C A B)
      (@terminal_arrow_test_incoming C t T A (@chain_pair_outgoing_diagram C S A B D pair)
        (@fapp0 _ _ (@kernel_presentation_unlift_func C S t T W P A (@chain_pair_outgoing_diagram C S A B D pair)) (@chain_pair_selected_boundary C S W A B D pair)))
      (@computational_chain_pair_dnext C S A B D pair));

// This theorem compares the same W/V recipe; it does not run a CAS.
assert [C : Cat] [S : τ (@PreadditiveCategory C)] (C1 : τ (IsNCat (cat_succ cat_zero) C))
  [t : τ (Obj C)] [T : τ (@TerminalObject C t)] [T0 : τ (@TerminalObject (Op_cat C) t)]
  [W : τ (@HasComputationalKernels C S)] [V : τ (@HasComputationalCokernels C S)]
  (P : τ (@KernelPresentation C S t T W)) (Q : τ (@CokernelPresentation C S t T0 V))
  [A B D : τ (Obj C)] (pair : τ (@ComputationalChainPair C S A B D)) ⊢
  @chain_pair_zero_cone_homology_object_path C S C1 t T T0 W V P Q A B D pair
  : τ (@= (Obj C)
      (@fapp0 (@ZeroArrowCone_cat C t T) C
        (@zero_arrow_cone_homology_func C S C1 t T T0 W V P Q) (@chain_pair_zero_cone C S t T W P A B D pair))
      (@computational_cokernel_object C S A (@computational_kernel_object C S B D (@computational_chain_pair_d C S A B D pair) (W B D (@computational_chain_pair_d C S A B D pair))) (@chain_pair_selected_boundary C S W A B D pair)
        (V A (@computational_kernel_object C S B D (@computational_chain_pair_d C S A B D pair) (W B D (@computational_chain_pair_d C S A B D pair))) (@chain_pair_selected_boundary C S W A B D pair))));

// Whole inverse mates keep their next directed Hom action.
type λ C : Cat, λ S : τ (@PreadditiveCategory C), λ t : τ (Obj C),
  λ T : τ (@TerminalObject C t), λ W : τ (@HasComputationalKernels C S),
  λ P : τ (@KernelPresentation C S t T W), λ X : τ (Obj C),
  λ d : τ (Functor WalkingArrow_cat C),
  λ f : τ (Hom C X (@fapp0 (Functor_cat WalkingArrow_cat C) C (@kernel_presentation_func C S t T W P) d)),
  λ g : τ (Hom C X (@fapp0 (Functor_cat WalkingArrow_cat C) C (@kernel_presentation_func C S t T W P) d)),
  @fapp1_func _ _ (@kernel_presentation_unlift_func C S t T W P X d) f g;
