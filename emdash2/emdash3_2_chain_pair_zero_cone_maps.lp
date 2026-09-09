/* Complete native map entry from the ORIGINAL chain-map factor data. */
require open emdash.emdash3_2_kernel_presentation_boundary_naturality;
require open emdash.emdash3_2_chain_pair_diagram_maps;
require open emdash.emdash3_2_zero_arrow_cone_map_introduction;

symbol chain_pair_zero_cone_map [C : Cat] [S : τ (@PreadditiveCategory C)]
  (C1 : τ (IsNCat (cat_succ cat_zero) C)) [t : τ (Obj C)]
  [T : τ (@TerminalObject C t)] [W : τ (@HasComputationalKernels C S)]
  (P : τ (@KernelPresentation C S t T W))
  [A0 B0 D0 A1 B1 D1 : τ (Obj C)]
  [p0 : τ (@ComputationalChainPair C S A0 B0 D0)]
  [p1 : τ (@ComputationalChainPair C S A1 B1 D1)]
  (m : τ (@ComputationalChainPairMap C S A0 B0 D0 A1 B1 D1 p0 p1))
  : τ (Hom (@ZeroArrowCone_cat C t T)
      (@chain_pair_zero_cone C S t T W P A0 B0 D0 p0)
      (@chain_pair_zero_cone C S t T W P A1 B1 D1 p1))
≔ @zero_cone_map_from_lifts C S t T W P A0 A1
    (@chain_pair_outgoing_diagram C S A0 B0 D0 p0)
    (@chain_pair_outgoing_diagram C S A1 B1 D1 p1)
    (@chain_pair_selected_boundary C S W A0 B0 D0 p0)
    (@chain_pair_selected_boundary C S W A1 B1 D1 p1)
    (@computational_chain_pair_map_next C S A0 B0 D0 A1 B1 D1 p0 p1 m)
    (@chain_pair_outgoing_diagram_map C S C1 A0 B0 D0 A1 B1 D1 p0 p1 m)
    (@kernel_presentation_boundary_path C S t T W P A0 A1
      (@chain_pair_outgoing_diagram C S A0 B0 D0 p0)
      (@chain_pair_outgoing_diagram C S A1 B1 D1 p1)
      (@computational_chain_pair_cone C S A0 B0 D0 p0)
      (@computational_chain_pair_cone C S A1 B1 D1 p1)
      (@computational_chain_pair_map_next C S A0 B0 D0 A1 B1 D1 p0 p1 m)
      (@chain_pair_outgoing_diagram_map C S C1 A0 B0 D0 A1 B1 D1 p0 p1 m)
      (@eq_sym _ _ _ (@computational_chain_pair_map_upper_path C S A0 B0 D0 A1 B1 D1 p0 p1 m)));

// The equality-valued raw-map parameter is internalized without a new owner.
symbol chain_pair_zero_cone_map_func [C : Cat] [S : τ (@PreadditiveCategory C)]
  (C1 : τ (IsNCat (cat_succ cat_zero) C)) [t : τ (Obj C)]
  [T : τ (@TerminalObject C t)] [W : τ (@HasComputationalKernels C S)]
  (P : τ (@KernelPresentation C S t T W))
  [A0 B0 D0 A1 B1 D1 : τ (Obj C)]
  (p0 : τ (@ComputationalChainPair C S A0 B0 D0))
  (p1 : τ (@ComputationalChainPair C S A1 B1 D1))
  : τ (Functor
      (Path_cat (@ComputationalChainPairMap C S A0 B0 D0 A1 B1 D1 p0 p1))
      (Hom_cat (@ZeroArrowCone_cat C t T)
        (@chain_pair_zero_cone C S t T W P A0 B0 D0 p0)
        (@chain_pair_zero_cone C S t T W P A1 B1 D1 p1)))
≔ @fapp0 _ _ (@path_lift_func
    (@ComputationalChainPairMap C S A0 B0 D0 A1 B1 D1 p0 p1)
    (Hom_cat (@ZeroArrowCone_cat C t T)
      (@chain_pair_zero_cone C S t T W P A0 B0 D0 p0)
      (@chain_pair_zero_cone C S t T W P A1 B1 D1 p1)))
    (λ m : τ (@ComputationalChainPairMap C S A0 B0 D0 A1 B1 D1 p0 p1),
      @chain_pair_zero_cone_map C S C1 t T W P A0 B0 D0 A1 B1 D1 p0 p1 m);
