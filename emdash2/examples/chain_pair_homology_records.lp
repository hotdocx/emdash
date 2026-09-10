/* Original-input records retain whole H and its actual beta component. */
require open emdash.emdash3_2_chain_pair_homology_records;

assert [C : Cat] [S : τ (@PreadditiveCategory C)]
  (C1 : τ (IsNCat (cat_succ cat_zero) C))
  [t : τ (Obj C)] [T : τ (@TerminalObject C t)] [T0 : τ (@TerminalObject (Op_cat C) t)]
  [W : τ (@HasComputationalKernels C S)] [V : τ (@HasComputationalCokernels C S)]
  (P : τ (@KernelPresentation C S t T W)) (Q : τ (@CokernelPresentation C S t T0 V))
  [A B D : τ (Obj C)] (pair : τ (@ComputationalChainPair C S A B D)) ⊢
  @homology_record_object C S A B D pair (@chain_pair_homology_record C S C1 t T T0 W V P Q A B D pair)
  ≡ @fapp0 (@ZeroArrowCone_cat C t T) C
      (@zero_arrow_cone_homology_func C S C1 t T T0 W V P Q)
      (@chain_pair_zero_cone C S t T W P A B D pair);

assert [C : Cat] [S : τ (@PreadditiveCategory C)]
  (C1 : τ (IsNCat (cat_succ cat_zero) C))
  [t : τ (Obj C)] [T : τ (@TerminalObject C t)] [T0 : τ (@TerminalObject (Op_cat C) t)]
  [W : τ (@HasComputationalKernels C S)] [V : τ (@HasComputationalCokernels C S)]
  (P : τ (@KernelPresentation C S t T W)) (Q : τ (@CokernelPresentation C S t T0 V))
  [A B D : τ (Obj C)] (pair : τ (@ComputationalChainPair C S A B D)) ⊢
  @homology_record_boundary C S A B D pair (@chain_pair_homology_record C S C1 t T T0 W V P Q A B D pair)
  ≡ @tapp0_fapp0 (@ZeroArrowCone_cat C t T) C
      (@zero_arrow_cone_first_func C t T)
      (@kernel_family_func (@ZeroArrowCone_cat C t T) C S t T W P (@zero_arrow_cone_diagram_func C t T))
      (@chain_pair_zero_cone C S t T W P A B D pair)
      (@kernel_family_boundary_transf (@ZeroArrowCone_cat C t T) C S t T W P
        (@zero_arrow_cone_first_func C t T) (@zero_arrow_cone_diagram_func C t T)
        (@zero_arrow_cone_universal_transf C C1 t T));
