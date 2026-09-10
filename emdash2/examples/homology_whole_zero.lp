/* Conditional zero identity at the original whole-H point. */
require open emdash.emdash3_2_homology_whole_zero;

assert [C : Cat] (S : τ (@PreadditiveCategory C))
  (C1 : τ (IsNCat (cat_succ cat_zero) C))
  [t : τ (Obj C)] (T : τ (@TerminalObject C t)) (T0 : τ (@TerminalObject (Op_cat C) t))
  [W : τ (@HasComputationalKernels C S)] [V : τ (@HasComputationalCokernels C S)]
  (KP : τ (@KernelPresentation C S t T W)) (QP : τ (@CokernelPresentation C S t T0 V))
  [A B D : τ (Obj C)] (pair : τ (@ComputationalChainPair C S A B D))
  (TB : τ (@TerminalObject C B)) ⊢
  @homology_whole_terminal_middle_zero C S C1 t T T0 W V KP QP A B D pair TB : τ (@= (Hom C (@fapp0
    (@ZeroArrowCone_cat C t T) C
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
      (@chain_pair_zero_cone C S t T W KP A B D pair))));

// The theorem is conditional, not a new global runtime identity collapse.
assertnot [C : Cat] (S : τ (@PreadditiveCategory C))
  (C1 : τ (IsNCat (cat_succ cat_zero) C))
  [t : τ (Obj C)] (T : τ (@TerminalObject C t)) (T0 : τ (@TerminalObject (Op_cat C) t))
  [W : τ (@HasComputationalKernels C S)] [V : τ (@HasComputationalCokernels C S)]
  (KP : τ (@KernelPresentation C S t T W)) (QP : τ (@CokernelPresentation C S t T0 V))
  [A B D : τ (Obj C)] (pair : τ (@ComputationalChainPair C S A B D)) ⊢ @id C (@fapp0 (@ZeroArrowCone_cat C t T) C
      (@zero_arrow_cone_homology_func C S C1 t T T0 W V KP QP)
      (@chain_pair_zero_cone C S t T W KP A B D pair)) ≡ @preadditive_hom_zero C S (@fapp0 (@ZeroArrowCone_cat C t
        T) C
      (@zero_arrow_cone_homology_func C S C1 t T T0 W V KP QP)
      (@chain_pair_zero_cone C S t T W KP A B D pair)) (@fapp0 (@ZeroArrowCone_cat C t T) C
      (@zero_arrow_cone_homology_func C S C1 t T T0 W V KP QP)
      (@chain_pair_zero_cone C S t T W KP A B D pair));
