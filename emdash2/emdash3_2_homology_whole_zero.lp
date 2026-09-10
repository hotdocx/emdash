/* The zero-middle theorem at the actual whole-H application. */
require open emdash.emdash3_2_homology_record_zero;
require open emdash.emdash3_2_chain_pair_homology_records;

symbol homology_whole_middle_zero [C : Cat] (S : τ (@PreadditiveCategory C))
  (C1 : τ (IsNCat (cat_succ cat_zero) C))
  [t : τ (Obj C)] (T : τ (@TerminalObject C t)) (T0 : τ (@TerminalObject (Op_cat C) t))
  [W : τ (@HasComputationalKernels C S)] [V : τ (@HasComputationalCokernels C S)]
  (KP : τ (@KernelPresentation C S t T W)) (QP : τ (@CokernelPresentation C S t T0 V))
  [A B D : τ (Obj C)] (pair : τ (@ComputationalChainPair C S A B D))
  (zero_B : τ (@= (Hom C B B) (@id C B) (@preadditive_hom_zero C S B B)))
  : τ (@= (Hom C (@fapp0 (@ZeroArrowCone_cat C t T) C
      (@zero_arrow_cone_homology_func C S C1 t T T0 W V KP QP)
      (@chain_pair_zero_cone C S t T W KP A B D pair)) (@fapp0 (@ZeroArrowCone_cat C t T) C
      (@zero_arrow_cone_homology_func C S C1 t T T0 W V KP QP)
      (@chain_pair_zero_cone C S t T W KP A B D pair))) (@id C (@fapp0 (@ZeroArrowCone_cat C t T) C
      (@zero_arrow_cone_homology_func C S C1 t T T0 W V KP QP)
      (@chain_pair_zero_cone C S t T W KP A B D pair))) (@preadditive_hom_zero C S (@fapp0 (@ZeroArrowCone_cat C t
        T) C
      (@zero_arrow_cone_homology_func C S C1 t T T0 W V KP QP)
      (@chain_pair_zero_cone C S t T W KP A B D pair)) (@fapp0 (@ZeroArrowCone_cat C t T) C
      (@zero_arrow_cone_homology_func C S C1 t T T0 W V KP QP)
      (@chain_pair_zero_cone C S t T W KP A B D pair))))
≔ @homology_record_middle_zero C S A B D pair
    (@chain_pair_homology_record C S C1 t T T0 W V KP QP A B D pair) zero_B;

symbol homology_whole_terminal_middle_zero [C : Cat] (S : τ (@PreadditiveCategory C))
  (C1 : τ (IsNCat (cat_succ cat_zero) C))
  [t : τ (Obj C)] (T : τ (@TerminalObject C t)) (T0 : τ (@TerminalObject (Op_cat C) t))
  [W : τ (@HasComputationalKernels C S)] [V : τ (@HasComputationalCokernels C S)]
  (KP : τ (@KernelPresentation C S t T W)) (QP : τ (@CokernelPresentation C S t T0 V))
  [A B D : τ (Obj C)] (pair : τ (@ComputationalChainPair C S A B D))
  (TB : τ (@TerminalObject C B))
  : τ (@= (Hom C (@fapp0 (@ZeroArrowCone_cat C t T) C
      (@zero_arrow_cone_homology_func C S C1 t T T0 W V KP QP)
      (@chain_pair_zero_cone C S t T W KP A B D pair)) (@fapp0 (@ZeroArrowCone_cat C t T) C
      (@zero_arrow_cone_homology_func C S C1 t T T0 W V KP QP)
      (@chain_pair_zero_cone C S t T W KP A B D pair))) (@id C (@fapp0 (@ZeroArrowCone_cat C t T) C
      (@zero_arrow_cone_homology_func C S C1 t T T0 W V KP QP)
      (@chain_pair_zero_cone C S t T W KP A B D pair))) (@preadditive_hom_zero C S (@fapp0 (@ZeroArrowCone_cat C t
        T) C
      (@zero_arrow_cone_homology_func C S C1 t T T0 W V KP QP)
      (@chain_pair_zero_cone C S t T W KP A B D pair)) (@fapp0 (@ZeroArrowCone_cat C t T) C
      (@zero_arrow_cone_homology_func C S C1 t T T0 W V KP QP)
      (@chain_pair_zero_cone C S t T W KP A B D pair))))
≔ @homology_whole_middle_zero C S C1 t T T0 W V KP QP A B D pair
    (@preadditive_terminal_identity_zero_path C S B TB);
