/*
  Original chain maps act through the existing native category and whole H.
  Whole fixed-pair action functors retain the raw-map parameter's action;
  point aliases observe those functors. Reconstruction follows from whole
  naturality, without caller-supplied square equations or a second map algorithm.
*/
require open emdash.emdash3_2_homology_family_map_factors;
require open emdash.emdash3_2_chain_pair_zero_cone_maps;
require open emdash.emdash3_2_chain_pair_homology_records;
require open emdash.emdash3_2_homology_record_cancellation;

// These whole fixed-pair views retain action on the raw-map parameter.
symbol chain_pair_homology_cycle_action_func
  [C : Cat] [S : τ (@PreadditiveCategory C)]
  (C1 : τ (IsNCat (cat_succ cat_zero) C))
  [t : τ (Obj C)] [T : τ (@TerminalObject C t)]
  [W : τ (@HasComputationalKernels C S)]
  (P : τ (@KernelPresentation C S t T W))
  [A0 B0 D0 A1 B1 D1 : τ (Obj C)]
  (p0 : τ (@ComputationalChainPair C S A0 B0 D0))
  (p1 : τ (@ComputationalChainPair C S A1 B1 D1))
  : τ (Functor (Path_cat (@ComputationalChainPairMap C S A0 B0 D0 A1 B1 D1 p0 p1)) (Hom_cat C (@fapp0 (@ZeroArrowCone_cat C t T) C
    (@kernel_family_func (@ZeroArrowCone_cat C t T) C S t T W P (@zero_arrow_cone_diagram_func C t T)) (@chain_pair_zero_cone C S t
    T W P A0 B0 D0 p0)) (@fapp0 (@ZeroArrowCone_cat C t T) C (@kernel_family_func (@ZeroArrowCone_cat C t T) C S t T W P
    (@zero_arrow_cone_diagram_func C t T)) (@chain_pair_zero_cone C S t T W P A1 B1 D1 p1))))
≔ @comp_cat_fapp0 (Path_cat (@ComputationalChainPairMap C S A0 B0 D0 A1 B1 D1 p0 p1)) (Hom_cat (@ZeroArrowCone_cat C t T)
  (@chain_pair_zero_cone C S t T W P A0 B0 D0 p0) (@chain_pair_zero_cone C S t T W P A1 B1 D1 p1)) (Hom_cat C (@fapp0
  (@ZeroArrowCone_cat C t T) C (@kernel_family_func (@ZeroArrowCone_cat C t T) C S t T W P (@zero_arrow_cone_diagram_func C t T))
  (@chain_pair_zero_cone C S t T W P A0 B0 D0 p0)) (@fapp0 (@ZeroArrowCone_cat C t T) C (@kernel_family_func (@ZeroArrowCone_cat C t
  T) C S t T W P (@zero_arrow_cone_diagram_func C t T)) (@chain_pair_zero_cone C S t T W P A1 B1 D1 p1)))
    (@fapp1_func (@ZeroArrowCone_cat C t T) C (@kernel_family_func (@ZeroArrowCone_cat C t T) C S t T W P
      (@zero_arrow_cone_diagram_func C t T)) (@chain_pair_zero_cone C S t T W P A0 B0 D0 p0) (@chain_pair_zero_cone C S t T W P A1
      B1 D1 p1)) (@chain_pair_zero_cone_map_func C S C1 t T W P A0 B0 D0 A1 B1 D1 p0 p1);

symbol chain_pair_homology_action_func
  [C : Cat] [S : τ (@PreadditiveCategory C)]
  (C1 : τ (IsNCat (cat_succ cat_zero) C))
  [t : τ (Obj C)] [T : τ (@TerminalObject C t)] [T0 : τ (@TerminalObject (Op_cat C) t)]
  [W : τ (@HasComputationalKernels C S)] [V : τ (@HasComputationalCokernels C S)]
  (P : τ (@KernelPresentation C S t T W)) (Q : τ (@CokernelPresentation C S t T0 V))
  [A0 B0 D0 A1 B1 D1 : τ (Obj C)]
  (p0 : τ (@ComputationalChainPair C S A0 B0 D0))
  (p1 : τ (@ComputationalChainPair C S A1 B1 D1))
  : τ (Functor (Path_cat (@ComputationalChainPairMap C S A0 B0 D0 A1 B1 D1 p0 p1)) (Hom_cat C (@fapp0 (@ZeroArrowCone_cat C t T) C
    (@zero_arrow_cone_homology_func C S C1 t T T0 W V P Q) (@chain_pair_zero_cone C S t T W P A0 B0 D0 p0)) (@fapp0
    (@ZeroArrowCone_cat C t T) C (@zero_arrow_cone_homology_func C S C1 t T T0 W V P Q) (@chain_pair_zero_cone C S t T W P A1 B1 D1
    p1))))
≔ @comp_cat_fapp0 (Path_cat (@ComputationalChainPairMap C S A0 B0 D0 A1 B1 D1 p0 p1)) (Hom_cat (@ZeroArrowCone_cat C t T)
  (@chain_pair_zero_cone C S t T W P A0 B0 D0 p0) (@chain_pair_zero_cone C S t T W P A1 B1 D1 p1)) (Hom_cat C (@fapp0
  (@ZeroArrowCone_cat C t T) C (@zero_arrow_cone_homology_func C S C1 t T T0 W V P Q) (@chain_pair_zero_cone C S t T W P A0 B0 D0
  p0)) (@fapp0 (@ZeroArrowCone_cat C t T) C (@zero_arrow_cone_homology_func C S C1 t T T0 W V P Q) (@chain_pair_zero_cone C S t T W
  P A1 B1 D1 p1)))
    (@fapp1_func (@ZeroArrowCone_cat C t T) C (@zero_arrow_cone_homology_func C S C1 t T T0 W V P Q) (@chain_pair_zero_cone C S t T
      W P A0 B0 D0 p0) (@chain_pair_zero_cone C S t T W P A1 B1 D1 p1)) (@chain_pair_zero_cone_map_func C S C1 t T W P A0 B0 D0 A1
      B1 D1 p0 p1);

// Transparent point observations of those whole functors.
symbol chain_pair_homology_cycle_action
  [C : Cat] [S : τ (@PreadditiveCategory C)]
  (C1 : τ (IsNCat (cat_succ cat_zero) C))
  [t : τ (Obj C)] [T : τ (@TerminalObject C t)]
  [W : τ (@HasComputationalKernels C S)]
  (P : τ (@KernelPresentation C S t T W))
  [A0 B0 D0 A1 B1 D1 : τ (Obj C)]
  (p0 : τ (@ComputationalChainPair C S A0 B0 D0))
  (p1 : τ (@ComputationalChainPair C S A1 B1 D1)) (m : τ (@ComputationalChainPairMap C S A0 B0 D0 A1 B1 D1 p0 p1))
  : τ (Hom C (@fapp0 (@ZeroArrowCone_cat C t T) C (@kernel_family_func (@ZeroArrowCone_cat C t T) C S t T W P
    (@zero_arrow_cone_diagram_func C t T)) (@chain_pair_zero_cone C S t T W P A0 B0 D0 p0)) (@fapp0 (@ZeroArrowCone_cat C t T) C
    (@kernel_family_func (@ZeroArrowCone_cat C t T) C S t T W P (@zero_arrow_cone_diagram_func C t T)) (@chain_pair_zero_cone C S t
    T W P A1 B1 D1 p1)))
≔ @fapp0 (Path_cat (@ComputationalChainPairMap C S A0 B0 D0 A1 B1 D1 p0 p1)) (Hom_cat C (@fapp0 (@ZeroArrowCone_cat C t T) C
  (@kernel_family_func (@ZeroArrowCone_cat C t T) C S t T W P (@zero_arrow_cone_diagram_func C t T)) (@chain_pair_zero_cone C S t T
  W P A0 B0 D0 p0)) (@fapp0 (@ZeroArrowCone_cat C t T) C (@kernel_family_func (@ZeroArrowCone_cat C t T) C S t T W P
  (@zero_arrow_cone_diagram_func C t T)) (@chain_pair_zero_cone C S t T W P A1 B1 D1 p1)))
    (@chain_pair_homology_cycle_action_func C S C1 t T W P A0 B0 D0 A1 B1 D1 p0 p1) m;

symbol chain_pair_homology_action
  [C : Cat] [S : τ (@PreadditiveCategory C)]
  (C1 : τ (IsNCat (cat_succ cat_zero) C))
  [t : τ (Obj C)] [T : τ (@TerminalObject C t)] [T0 : τ (@TerminalObject (Op_cat C) t)]
  [W : τ (@HasComputationalKernels C S)] [V : τ (@HasComputationalCokernels C S)]
  (P : τ (@KernelPresentation C S t T W)) (Q : τ (@CokernelPresentation C S t T0 V))
  [A0 B0 D0 A1 B1 D1 : τ (Obj C)]
  (p0 : τ (@ComputationalChainPair C S A0 B0 D0))
  (p1 : τ (@ComputationalChainPair C S A1 B1 D1)) (m : τ (@ComputationalChainPairMap C S A0 B0 D0 A1 B1 D1 p0 p1))
  : τ (Hom C (@fapp0 (@ZeroArrowCone_cat C t T) C (@zero_arrow_cone_homology_func C S C1 t T T0 W V P Q) (@chain_pair_zero_cone C S
    t T W P A0 B0 D0 p0)) (@fapp0 (@ZeroArrowCone_cat C t T) C (@zero_arrow_cone_homology_func C S C1 t T T0 W V P Q)
    (@chain_pair_zero_cone C S t T W P A1 B1 D1 p1)))
≔ @fapp0 (Path_cat (@ComputationalChainPairMap C S A0 B0 D0 A1 B1 D1 p0 p1)) (Hom_cat C (@fapp0 (@ZeroArrowCone_cat C t T) C
  (@zero_arrow_cone_homology_func C S C1 t T T0 W V P Q) (@chain_pair_zero_cone C S t T W P A0 B0 D0 p0)) (@fapp0
  (@ZeroArrowCone_cat C t T) C (@zero_arrow_cone_homology_func C S C1 t T T0 W V P Q) (@chain_pair_zero_cone C S t T W P A1 B1 D1
  p1)))
    (@chain_pair_homology_action_func C S C1 t T T0 W V P Q A0 B0 D0 A1 B1 D1 p0 p1) m;

// No reconstruction square is an extra input: it is the actual q naturality.
symbol chain_pair_homology_action_factor
  [C : Cat] [S : τ (@PreadditiveCategory C)]
  (C1 : τ (IsNCat (cat_succ cat_zero) C))
  [t : τ (Obj C)] [T : τ (@TerminalObject C t)] [T0 : τ (@TerminalObject (Op_cat C) t)]
  [W : τ (@HasComputationalKernels C S)] [V : τ (@HasComputationalCokernels C S)]
  (P : τ (@KernelPresentation C S t T W)) (Q : τ (@CokernelPresentation C S t T0 V))
  [A0 B0 D0 A1 B1 D1 : τ (Obj C)]
  (p0 : τ (@ComputationalChainPair C S A0 B0 D0))
  (p1 : τ (@ComputationalChainPair C S A1 B1 D1)) (m : τ (@ComputationalChainPairMap C S A0 B0 D0 A1 B1 D1 p0 p1))
  : τ (@HomPrecompFactor C (@homology_record_cycle_object C S A0 B0 D0 p0 (@chain_pair_homology_record C S C1 t T T0 W V P Q A0 B0
    D0 p0)) (@homology_record_object C S A0 B0 D0 p0 (@chain_pair_homology_record C S C1 t T T0 W V P Q A0 B0 D0 p0))
    (@homology_record_object C S A1 B1 D1 p1 (@chain_pair_homology_record C S C1 t T T0 W V P Q A1 B1 D1 p1))
      (@homology_record_projection C S A0 B0 D0 p0 (@chain_pair_homology_record C S C1 t T T0 W V P Q A0 B0 D0 p0)) (@comp_fapp0 C
        (@homology_record_cycle_object C S A0 B0 D0 p0 (@chain_pair_homology_record C S C1 t T T0 W V P Q A0 B0 D0 p0))
        (@homology_record_cycle_object C S A1 B1 D1 p1 (@chain_pair_homology_record C S C1 t T T0 W V P Q A1 B1 D1 p1))
        (@homology_record_object C S A1 B1 D1 p1 (@chain_pair_homology_record C S C1 t T T0 W V P Q A1 B1 D1 p1))
        (@homology_record_projection C S A1 B1 D1 p1 (@chain_pair_homology_record C S C1 t T T0 W V P Q A1 B1 D1 p1))
        (@chain_pair_homology_cycle_action C S C1 t T W P A0 B0 D0 A1 B1 D1 p0 p1 m)))
≔ @homology_family_record_map_factor (@ZeroArrowCone_cat C t T) C S t T T0 W V P Q (@zero_arrow_cone_first_func C t T)
  (@zero_arrow_cone_diagram_func C t T) (@zero_arrow_cone_universal_transf C C1 t T)
    (@chain_pair_zero_cone C S t T W P A0 B0 D0 p0) (@chain_pair_zero_cone C S t T W P A1 B1 D1 p1) (@chain_pair_zero_cone_map C S
      C1 t T W P A0 B0 D0 A1 B1 D1 p0 p1 m);

symbol chain_pair_homology_cycle_action_factor
  [C : Cat] [S : τ (@PreadditiveCategory C)]
  (C1 : τ (IsNCat (cat_succ cat_zero) C))
  [t : τ (Obj C)] [T : τ (@TerminalObject C t)] [T0 : τ (@TerminalObject (Op_cat C) t)]
  [W : τ (@HasComputationalKernels C S)] [V : τ (@HasComputationalCokernels C S)]
  (P : τ (@KernelPresentation C S t T W)) (Q : τ (@CokernelPresentation C S t T0 V))
  [A0 B0 D0 A1 B1 D1 : τ (Obj C)]
  (p0 : τ (@ComputationalChainPair C S A0 B0 D0))
  (p1 : τ (@ComputationalChainPair C S A1 B1 D1)) (m : τ (@ComputationalChainPairMap C S A0 B0 D0 A1 B1 D1 p0 p1))
  : τ (@HomPostcompFactor C (@homology_record_cycle_object C S A1 B1 D1 p1 (@chain_pair_homology_record C S C1 t T T0 W V P Q A1 B1
    D1 p1)) B1 (@homology_record_cycle_object C S A0 B0 D0 p0 (@chain_pair_homology_record C S C1 t T T0 W V P Q A0 B0 D0 p0))
      (@homology_record_cycle_embedding C S A1 B1 D1 p1 (@chain_pair_homology_record C S C1 t T T0 W V P Q A1 B1 D1 p1))
        (@comp_fapp0 C (@homology_record_cycle_object C S A0 B0 D0 p0 (@chain_pair_homology_record C S C1 t T T0 W V P Q A0 B0 D0
        p0)) B0 B1 (@computational_chain_pair_map_middle C S A0 B0 D0 A1 B1 D1 p0 p1 m) (@homology_record_cycle_embedding C S A0 B0
        D0 p0 (@chain_pair_homology_record C S C1 t T T0 W V P Q A0 B0 D0 p0))))
≔ @homology_family_record_cycle_factor (@ZeroArrowCone_cat C t T) C S t T T0 W V P Q (@zero_arrow_cone_first_func C t T)
  (@zero_arrow_cone_diagram_func C t T) (@zero_arrow_cone_universal_transf C C1 t T)
    (@chain_pair_zero_cone C S t T W P A0 B0 D0 p0) (@chain_pair_zero_cone C S t T W P A1 B1 D1 p1) (@chain_pair_zero_cone_map C S
      C1 t T W P A0 B0 D0 A1 B1 D1 p0 p1 m);

symbol chain_pair_homology_action_middle_zero
  [C : Cat] [S : τ (@PreadditiveCategory C)]
  (C1 : τ (IsNCat (cat_succ cat_zero) C))
  [t : τ (Obj C)] [T : τ (@TerminalObject C t)] [T0 : τ (@TerminalObject (Op_cat C) t)]
  [W : τ (@HasComputationalKernels C S)] [V : τ (@HasComputationalCokernels C S)]
  (P : τ (@KernelPresentation C S t T W)) (Q : τ (@CokernelPresentation C S t T0 V))
  [A0 B0 D0 A1 B1 D1 : τ (Obj C)]
  (p0 : τ (@ComputationalChainPair C S A0 B0 D0))
  (p1 : τ (@ComputationalChainPair C S A1 B1 D1)) (m : τ (@ComputationalChainPairMap C S A0 B0 D0 A1 B1 D1 p0 p1))
  (zero : τ (@= (Hom C B0 B1) (@computational_chain_pair_map_middle C S A0 B0 D0 A1 B1 D1 p0 p1 m) (@preadditive_hom_zero C S B0
    B1)))
  : τ (@= (Hom C (@homology_record_object C S A0 B0 D0 p0 (@chain_pair_homology_record C S C1 t T T0 W V P Q A0 B0 D0 p0))
    (@homology_record_object C S A1 B1 D1 p1 (@chain_pair_homology_record C S C1 t T T0 W V P Q A1 B1 D1 p1)))
    (@chain_pair_homology_action C S C1 t T T0 W V P Q A0 B0 D0 A1 B1 D1 p0 p1 m) (@preadditive_hom_zero C S
    (@homology_record_object C S A0 B0 D0 p0 (@chain_pair_homology_record C S C1 t T T0 W V P Q A0 B0 D0 p0))
    (@homology_record_object C S A1 B1 D1 p1 (@chain_pair_homology_record C S C1 t T T0 W V P Q A1 B1 D1 p1))))
≔ @homology_record_map_factor_middle_zero C S A0 B0 D0 A1 B1 D1 p0 p1
    (@chain_pair_homology_record C S C1 t T T0 W V P Q A0 B0 D0 p0) (@chain_pair_homology_record C S C1 t T T0 W V P Q A1 B1 D1 p1)
      (@computational_chain_pair_map_middle C S A0 B0 D0 A1 B1 D1 p0 p1 m) (@chain_pair_homology_cycle_action_factor C S C1 t T T0 W
      V P Q A0 B0 D0 A1 B1 D1 p0 p1 m) (@chain_pair_homology_action_factor C S C1 t T T0 W V P Q A0 B0 D0 A1 B1 D1 p0 p1 m) zero;
