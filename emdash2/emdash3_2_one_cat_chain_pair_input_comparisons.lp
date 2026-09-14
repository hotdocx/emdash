/* Comparison of the original inverse-mate input with the direct raw input. */
require open emdash.emdash3_2_one_cat_zero_cone_fibre_inclusion;
require open emdash.emdash3_2_chain_pair_zero_cone_comparisons;
require open emdash.emdash3_2_one_cat_chain_pair_inputs;
require open emdash.emdash3_2_one_cat_diagram_map_paths;

// Observe the existing input's actual transformation, without reconstructing it.
symbol chain_pair_retained_transf [C : Cat] [S : τ (@PreadditiveCategory C)]
  [t : τ (Obj C)] [T : τ (@TerminalObject C t)] [W : τ (@HasComputationalKernels C S)]
  (P : τ (@KernelPresentation C S t T W))
  [A B D : τ (Obj C)] (pair : τ (@ComputationalChainPair C S A B D))
  : τ (@Transf WalkingArrow_cat C
      (@fapp0 C (Functor_cat WalkingArrow_cat C) (@terminal_arrow_diagram_func C t T) A)
      (@chain_pair_outgoing_diagram C S A B D pair))
≔ sigma_Snd (sigma_Snd (@chain_pair_zero_cone C S t T W P A B D pair));

// Ordinary reflection compares the whole transformations using derived observations.
symbol chain_pair_retained_native_transf_path [C : Cat] [S : τ (@PreadditiveCategory C)]
  (C1 : τ (IsNCat (cat_succ cat_zero) C))
  [t : τ (Obj C)] [T : τ (@TerminalObject C t)] [W : τ (@HasComputationalKernels C S)]
  (P : τ (@KernelPresentation C S t T W))
  [A B D : τ (Obj C)] (pair : τ (@ComputationalChainPair C S A B D))
  : τ (@= (@Transf WalkingArrow_cat C
      (@fapp0 C (Functor_cat WalkingArrow_cat C) (@terminal_arrow_diagram_func C t T) A)
      (@chain_pair_outgoing_diagram C S A B D pair))
      (@chain_pair_retained_transf C S t T W P A B D pair)
      (@chain_pair_native_transf C S C1 t T A B D pair))
≔ @one_cat_diagram_map_path C C1
    (@fapp0 C (Functor_cat WalkingArrow_cat C) (@terminal_arrow_diagram_func C t T) A)
    (@chain_pair_outgoing_diagram C S A B D pair)
    (@chain_pair_retained_transf C S t T W P A B D pair)
    (@chain_pair_native_transf C S C1 t T A B D pair)
    (@chain_pair_zero_cone_incoming_path C S t T W P A B D pair)
    (@preadditive_terminal_to_zero_path C S t D T
      (@terminal_arrow_test_tip C t T A (@chain_pair_outgoing_diagram C S A B D pair)
        (@chain_pair_retained_transf C S t T W P A B D pair)));

// The comparison arrow is whole fibre inclusion applied to the derived fibre path.
symbol chain_pair_retained_native_map [C : Cat] [S : τ (@PreadditiveCategory C)]
  (C1 : τ (IsNCat (cat_succ cat_zero) C))
  [t : τ (Obj C)] [T : τ (@TerminalObject C t)] [W : τ (@HasComputationalKernels C S)]
  (P : τ (@KernelPresentation C S t T W))
  [A B D : τ (Obj C)] (pair : τ (@ComputationalChainPair C S A B D))
  : τ (Hom (@ZeroArrowCone_cat C t T)
      (@chain_pair_zero_cone C S t T W P A B D pair)
      (@chain_pair_native_cone C S C1 t T A B D pair))
≔ @fapp1_fapp0
    (@Transf_cat WalkingArrow_cat C
      (@fapp0 C (Functor_cat WalkingArrow_cat C) (@terminal_arrow_diagram_func C t T) A)
      (@chain_pair_outgoing_diagram C S A B D pair))
    (@ZeroArrowCone_cat C t T)
    (@zero_arrow_cone_fibre_inclusion_func C C1 t T A (@chain_pair_outgoing_diagram C S A B D pair))
    (@chain_pair_retained_transf C S t T W P A B D pair)
    (@chain_pair_native_transf C S C1 t T A B D pair)
    (@path_to_hom (@Transf_cat WalkingArrow_cat C
      (@fapp0 C (Functor_cat WalkingArrow_cat C) (@terminal_arrow_diagram_func C t T) A)
      (@chain_pair_outgoing_diagram C S A B D pair))
      (@chain_pair_retained_transf C S t T W P A B D pair)
      (@chain_pair_native_transf C S C1 t T A B D pair)
      (@chain_pair_retained_native_transf_path C S C1 t T W P A B D pair));

// Existing fixed-forward equivalence action supplies the same comparison's inverse laws.
symbol chain_pair_retained_native_equiv [C : Cat] [S : τ (@PreadditiveCategory C)]
  (C1 : τ (IsNCat (cat_succ cat_zero) C))
  [t : τ (Obj C)] [T : τ (@TerminalObject C t)] [W : τ (@HasComputationalKernels C S)]
  (P : τ (@KernelPresentation C S t T W))
  [A B D : τ (Obj C)] (pair : τ (@ComputationalChainPair C S A B D))
  : τ (@OmegaEquivAlong (@ZeroArrowCone_cat C t T)
      (@chain_pair_zero_cone C S t T W P A B D pair)
      (@chain_pair_native_cone C S C1 t T A B D pair)
      (@chain_pair_retained_native_map C S C1 t T W P A B D pair))
≔ @omega_equiv_along_fapp1_fapp0
    (@Transf_cat WalkingArrow_cat C
      (@fapp0 C (Functor_cat WalkingArrow_cat C) (@terminal_arrow_diagram_func C t T) A)
      (@chain_pair_outgoing_diagram C S A B D pair)) (@ZeroArrowCone_cat C t T)
    (@zero_arrow_cone_fibre_inclusion_func C C1 t T A (@chain_pair_outgoing_diagram C S A B D pair))
    (@chain_pair_retained_transf C S t T W P A B D pair)
    (@chain_pair_native_transf C S C1 t T A B D pair)
    (@path_to_hom (@Transf_cat WalkingArrow_cat C
      (@fapp0 C (Functor_cat WalkingArrow_cat C) (@terminal_arrow_diagram_func C t T) A)
      (@chain_pair_outgoing_diagram C S A B D pair))
      (@chain_pair_retained_transf C S t T W P A B D pair)
      (@chain_pair_native_transf C S C1 t T A B D pair)
      (@chain_pair_retained_native_transf_path C S C1 t T W P A B D pair))
    (@object_path_equiv_along (@Transf_cat WalkingArrow_cat C
      (@fapp0 C (Functor_cat WalkingArrow_cat C) (@terminal_arrow_diagram_func C t T) A)
      (@chain_pair_outgoing_diagram C S A B D pair))
      (@chain_pair_retained_transf C S t T W P A B D pair)
      (@chain_pair_native_transf C S C1 t T A B D pair)
      (@chain_pair_retained_native_transf_path C S C1 t T W P A B D pair));
