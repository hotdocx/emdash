/*
  Boundary preservation from the actual whole beta transformation.
  This is the existing strict-profile naturality, not a new rule or an
  extra square required from a chain-map caller.
*/
require open emdash.emdash3_2_chain_pair_homology_actions;

symbol homology_family_boundary_naturality
  [B C : Cat] [S : τ (@PreadditiveCategory C)]
  [t : τ (Obj C)] [T : τ (@TerminalObject C t)] [W : τ (@HasComputationalKernels C S)]
  (P : τ (@KernelPresentation C S t T W))
  (A : τ (Functor B C)) (D : τ (Functor B (Functor_cat WalkingArrow_cat C)))
  (h : τ (@Transf B (Functor_cat WalkingArrow_cat C)
    (@comp_cat_fapp0 B C (Functor_cat WalkingArrow_cat C) (@terminal_arrow_diagram_func C t T) A) D)) [x y : τ (Obj B)] (p : τ (Hom
      B x y))
  : τ (@= (Hom C (@fapp0 B C A x) (@fapp0 B C (@kernel_family_func B C S t T W P D) y))
      (@comp_fapp0 C _ _ _ (@fapp1_fapp0 B C (@kernel_family_func B C S t T W P D) x y p) (@tapp0_fapp0 B C A (@kernel_family_func B
        C S t T W P D) x (@kernel_family_boundary_transf B C S t T W P A D h)))
      (@comp_fapp0 C _ _ _ (@tapp0_fapp0 B C A (@kernel_family_func B C S t T W P D) y (@kernel_family_boundary_transf B C S t T W P
        A D h)) (@fapp1_fapp0 B C A x y p)))
≔ @strict_component_naturality_path B C A (@kernel_family_func B C S t T W P D) (@kernel_family_boundary_transf B C S t T W P A D h)
  x y p;

symbol chain_pair_homology_boundary_action_path
  [C : Cat] [S : τ (@PreadditiveCategory C)]
  (C1 : τ (IsNCat (cat_succ cat_zero) C))
  [t : τ (Obj C)] [T : τ (@TerminalObject C t)] [T0 : τ (@TerminalObject (Op_cat C) t)]
  [W : τ (@HasComputationalKernels C S)] [V : τ (@HasComputationalCokernels C S)]
  (P : τ (@KernelPresentation C S t T W)) (Q : τ (@CokernelPresentation C S t T0 V))
  [A0 B0 D0 A1 B1 D1 : τ (Obj C)]
  (p0 : τ (@ComputationalChainPair C S A0 B0 D0))
  (p1 : τ (@ComputationalChainPair C S A1 B1 D1)) (m : τ (@ComputationalChainPairMap C S A0 B0 D0 A1 B1 D1 p0 p1))
  : τ (@= (Hom C A0 (@homology_record_cycle_object C S A1 B1 D1 p1 (@chain_pair_homology_record C S C1 t T T0 W V P Q A1 B1 D1 p1)))
      (@comp_fapp0 C A0 (@homology_record_cycle_object C S A0 B0 D0 p0 (@chain_pair_homology_record C S C1 t T T0 W V P Q A0 B0 D0
        p0)) (@homology_record_cycle_object C S A1 B1 D1 p1 (@chain_pair_homology_record C S C1 t T T0 W V P Q A1 B1 D1 p1))
        (@chain_pair_homology_cycle_action C S C1 t T W P A0 B0 D0 A1 B1 D1 p0 p1 m) (@homology_record_boundary C S A0 B0 D0 p0
        (@chain_pair_homology_record C S C1 t T T0 W V P Q A0 B0 D0 p0)))
      (@comp_fapp0 C A0 A1 (@homology_record_cycle_object C S A1 B1 D1 p1 (@chain_pair_homology_record C S C1 t T T0 W V P Q A1 B1
        D1 p1)) (@homology_record_boundary C S A1 B1 D1 p1 (@chain_pair_homology_record C S C1 t T T0 W V P Q A1 B1 D1 p1))
        (@computational_chain_pair_map_next C S A0 B0 D0 A1 B1 D1 p0 p1 m)))
≔ @homology_family_boundary_naturality (@ZeroArrowCone_cat C t T) C S t T W P (@zero_arrow_cone_first_func C t T)
  (@zero_arrow_cone_diagram_func C t T) (@zero_arrow_cone_universal_transf C C1 t T)
    (@chain_pair_zero_cone C S t T W P A0 B0 D0 p0) (@chain_pair_zero_cone C S t T W P A1 B1 D1 p1) (@chain_pair_zero_cone_map C S
      C1 t T W P A0 B0 D0 A1 B1 D1 p0 p1 m);
