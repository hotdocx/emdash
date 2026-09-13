/* Raw chain-pair input before kernel or cokernel selection.
   Existing native square action constructs the whole diagram transformation
   from the original differentials and chain-zero witness. */
require open emdash.emdash3_2_chain_pair_diagrams;
require open emdash.emdash3_2_one_cat_zero_arrow_inputs;

// Original raw fields supply the existing whole diagram transformation.
symbol chain_pair_native_transf [C : Cat] [S : τ (@PreadditiveCategory C)]
  (C1 : τ (IsNCat (cat_succ cat_zero) C))
  [t : τ (Obj C)] [T : τ (@TerminalObject C t)]
  [A B D : τ (Obj C)] (pair : τ (@ComputationalChainPair C S A B D))
  : τ (@Transf WalkingArrow_cat C
      (@fapp0 C (Functor_cat WalkingArrow_cat C) (@terminal_arrow_diagram_func C t T) A)
      (@chain_pair_outgoing_diagram C S A B D pair))
≔ @terminal_zero_composite_transf C S C1 t T A B D
    (@computational_chain_pair_dnext C S A B D pair)
    (@computational_chain_pair_d C S A B D pair)
    (@computational_chain_pair_path C S A B D pair);

// The input is formed before any kernel or cokernel structure is supplied.
symbol chain_pair_native_cone [C : Cat] [S : τ (@PreadditiveCategory C)]
  (C1 : τ (IsNCat (cat_succ cat_zero) C))
  [t : τ (Obj C)] [T : τ (@TerminalObject C t)]
  [A B D : τ (Obj C)] (pair : τ (@ComputationalChainPair C S A B D))
  : τ (Obj (@ZeroArrowCone_cat C t T))
≔ @zero_composite_native_cone C S C1 t T A B D
    (@computational_chain_pair_dnext C S A B D pair)
    (@computational_chain_pair_d C S A B D pair)
    (@computational_chain_pair_path C S A B D pair);
