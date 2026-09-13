/* Whole H action on direct native chain-pair maps.
   The raw-map realization is formed before P/Q are supplied. Composition
   with the original H Hom-functor retains the entire higher action. */
require open emdash.emdash3_2_one_cat_chain_pair_native_maps;
require open emdash.emdash3_2_zero_arrow_cone_adjunction_homology;

// Whole H Hom-action after the whole direct raw-map realization.
symbol chain_pair_adjunction_homology_map_func [C : Cat] [S : τ (@PreadditiveCategory C)]
  (C1 : τ (IsNCat (cat_succ cat_zero) C)) [t : τ (Obj C)]
  [T : τ (@TerminalObject C t)] [T0 : τ (@TerminalObject (Op_cat C) t)]
  (P : τ (@KernelAdjunctionStructure C S t T)) (Q : τ (@CokernelAdjunctionStructure C S t T0))
  [A0 B0 D0 A1 B1 D1 : τ (Obj C)]
  (p0 : τ (@ComputationalChainPair C S A0 B0 D0))
  (p1 : τ (@ComputationalChainPair C S A1 B1 D1))
  : τ (Functor (Path_cat (@ComputationalChainPairMap C S A0 B0 D0 A1 B1 D1 p0 p1)) (Hom_cat C (@fapp0 (@ZeroArrowCone_cat C t T) C (@zero_arrow_cone_adjunction_homology_func C S C1 t T T0 P Q) (@chain_pair_native_cone C S C1 t T A0 B0 D0 p0)) (@fapp0 (@ZeroArrowCone_cat C t T) C (@zero_arrow_cone_adjunction_homology_func C S C1 t T T0 P Q) (@chain_pair_native_cone C S C1 t T A1 B1 D1 p1))))
≔ @comp_cat_fapp0 (Path_cat (@ComputationalChainPairMap C S A0 B0 D0 A1 B1 D1 p0 p1)) (Hom_cat (@ZeroArrowCone_cat C t T) (@chain_pair_native_cone C S C1 t T A0 B0 D0 p0) (@chain_pair_native_cone C S C1 t T A1 B1 D1 p1)) (Hom_cat C (@fapp0 (@ZeroArrowCone_cat C t T) C (@zero_arrow_cone_adjunction_homology_func C S C1 t T T0 P Q) (@chain_pair_native_cone C S C1 t T A0 B0 D0 p0)) (@fapp0 (@ZeroArrowCone_cat C t T) C (@zero_arrow_cone_adjunction_homology_func C S C1 t T T0 P Q) (@chain_pair_native_cone C S C1 t T A1 B1 D1 p1)))
    (@fapp1_func (@ZeroArrowCone_cat C t T) C (@zero_arrow_cone_adjunction_homology_func C S C1 t T T0 P Q) (@chain_pair_native_cone C S C1 t T A0 B0 D0 p0) (@chain_pair_native_cone C S C1 t T A1 B1 D1 p1))
    (@chain_pair_native_map_func C S C1 t T A0 B0 D0 A1 B1 D1 p0 p1);

// Point view of that same whole map functor.
symbol chain_pair_adjunction_homology_map [C : Cat] [S : τ (@PreadditiveCategory C)]
  (C1 : τ (IsNCat (cat_succ cat_zero) C)) [t : τ (Obj C)]
  [T : τ (@TerminalObject C t)] [T0 : τ (@TerminalObject (Op_cat C) t)]
  (P : τ (@KernelAdjunctionStructure C S t T)) (Q : τ (@CokernelAdjunctionStructure C S t T0))
  [A0 B0 D0 A1 B1 D1 : τ (Obj C)]
  [p0 : τ (@ComputationalChainPair C S A0 B0 D0)]
  [p1 : τ (@ComputationalChainPair C S A1 B1 D1)]
  (m : τ (@ComputationalChainPairMap C S A0 B0 D0 A1 B1 D1 p0 p1))
  : τ (Hom C (@fapp0 (@ZeroArrowCone_cat C t T) C (@zero_arrow_cone_adjunction_homology_func C S C1 t T T0 P Q) (@chain_pair_native_cone C S C1 t T A0 B0 D0 p0)) (@fapp0 (@ZeroArrowCone_cat C t T) C (@zero_arrow_cone_adjunction_homology_func C S C1 t T T0 P Q) (@chain_pair_native_cone C S C1 t T A1 B1 D1 p1)))
≔ @fapp0 (Path_cat (@ComputationalChainPairMap C S A0 B0 D0 A1 B1 D1 p0 p1)) (Hom_cat C (@fapp0 (@ZeroArrowCone_cat C t T) C (@zero_arrow_cone_adjunction_homology_func C S C1 t T T0 P Q) (@chain_pair_native_cone C S C1 t T A0 B0 D0 p0)) (@fapp0 (@ZeroArrowCone_cat C t T) C (@zero_arrow_cone_adjunction_homology_func C S C1 t T T0 P Q) (@chain_pair_native_cone C S C1 t T A1 B1 D1 p1)))
    (@chain_pair_adjunction_homology_map_func C S C1 t T T0 P Q A0 B0 D0 A1 B1 D1 p0 p1) m;
