/* Whole H action at the direct native input and original record endpoints. */
require open emdash.emdash3_2_one_cat_chain_pair_homology_maps;
require open emdash.emdash3_2_one_cat_chain_pair_homology_records;

// The map is exactly the existing H applied to the direct native map.
assert [C : Cat] [S : τ (@PreadditiveCategory C)]
  (C1 : τ (IsNCat (cat_succ cat_zero) C)) [t : τ (Obj C)]
  [T : τ (@TerminalObject C t)] [T0 : τ (@TerminalObject (Op_cat C) t)]
  (P : τ (@KernelAdjunctionStructure C S t T)) (Q : τ (@CokernelAdjunctionStructure C S t T0))
  [A0 B0 D0 A1 B1 D1 : τ (Obj C)]
  (p0 : τ (@ComputationalChainPair C S A0 B0 D0))
  (p1 : τ (@ComputationalChainPair C S A1 B1 D1))
  (m : τ (@ComputationalChainPairMap C S A0 B0 D0 A1 B1 D1 p0 p1)) ⊢
  @chain_pair_adjunction_homology_map C S C1 t T T0 P Q A0 B0 D0 A1 B1 D1 p0 p1 m
  ≡ @fapp1_fapp0 (@ZeroArrowCone_cat C t T) C (@zero_arrow_cone_adjunction_homology_func C S C1 t T T0 P Q) (@chain_pair_native_cone C S C1 t T A0 B0 D0 p0) (@chain_pair_native_cone C S C1 t T A1 B1 D1 p1)
      (@chain_pair_native_map C S C1 t T A0 B0 D0 A1 B1 D1 p0 p1 m);

// Both H endpoints are the original-pair record observations.
assert [C : Cat] [S : τ (@PreadditiveCategory C)]
  (C1 : τ (IsNCat (cat_succ cat_zero) C)) [t : τ (Obj C)]
  [T : τ (@TerminalObject C t)] [T0 : τ (@TerminalObject (Op_cat C) t)]
  (P : τ (@KernelAdjunctionStructure C S t T)) (Q : τ (@CokernelAdjunctionStructure C S t T0))
  [A0 B0 D0 A1 B1 D1 : τ (Obj C)]
  (p0 : τ (@ComputationalChainPair C S A0 B0 D0))
  (p1 : τ (@ComputationalChainPair C S A1 B1 D1))
  (m : τ (@ComputationalChainPairMap C S A0 B0 D0 A1 B1 D1 p0 p1)) ⊢
  @chain_pair_adjunction_homology_map C S C1 t T T0 P Q A0 B0 D0 A1 B1 D1 p0 p1 m
  : τ (Hom C (@homology_record_object C S A0 B0 D0 p0 (@chain_pair_adjunction_homology_record C S C1 t T T0 P Q A0 B0 D0 p0)) (@homology_record_object C S A1 B1 D1 p1 (@chain_pair_adjunction_homology_record C S C1 t T T0 P Q A1 B1 D1 p1)));

// The whole map functor has those same record endpoints.
assert [C : Cat] [S : τ (@PreadditiveCategory C)]
  (C1 : τ (IsNCat (cat_succ cat_zero) C)) [t : τ (Obj C)]
  [T : τ (@TerminalObject C t)] [T0 : τ (@TerminalObject (Op_cat C) t)]
  (P : τ (@KernelAdjunctionStructure C S t T)) (Q : τ (@CokernelAdjunctionStructure C S t T0))
  [A0 B0 D0 A1 B1 D1 : τ (Obj C)]
  (p0 : τ (@ComputationalChainPair C S A0 B0 D0))
  (p1 : τ (@ComputationalChainPair C S A1 B1 D1))
  ⊢ @chain_pair_adjunction_homology_map_func C S C1 t T T0 P Q A0 B0 D0 A1 B1 D1 p0 p1
  : τ (Functor (Path_cat (@ComputationalChainPairMap C S A0 B0 D0 A1 B1 D1 p0 p1)) (Hom_cat C (@homology_record_object C S A0 B0 D0 p0 (@chain_pair_adjunction_homology_record C S C1 t T T0 P Q A0 B0 D0 p0)) (@homology_record_object C S A1 B1 D1 p1 (@chain_pair_adjunction_homology_record C S C1 t T T0 P Q A1 B1 D1 p1))));

// Another Hom action remains available, with no additional coherence input.
assert [C : Cat] [S : τ (@PreadditiveCategory C)]
  (C1 : τ (IsNCat (cat_succ cat_zero) C)) [t : τ (Obj C)]
  [T : τ (@TerminalObject C t)] [T0 : τ (@TerminalObject (Op_cat C) t)]
  (P : τ (@KernelAdjunctionStructure C S t T)) (Q : τ (@CokernelAdjunctionStructure C S t T0))
  [A0 B0 D0 A1 B1 D1 : τ (Obj C)]
  (p0 : τ (@ComputationalChainPair C S A0 B0 D0))
  (p1 : τ (@ComputationalChainPair C S A1 B1 D1))
  (m0 m1 : τ (@ComputationalChainPairMap C S A0 B0 D0 A1 B1 D1 p0 p1)) ⊢
  @fapp1_func _ _ (@chain_pair_adjunction_homology_map_func C S C1 t T T0 P Q A0 B0 D0 A1 B1 D1 p0 p1) m0 m1
  : τ (Functor (Hom_cat (Path_cat (@ComputationalChainPairMap C S A0 B0 D0 A1 B1 D1 p0 p1)) m0 m1)
      (Hom_cat (Hom_cat C (@homology_record_object C S A0 B0 D0 p0 (@chain_pair_adjunction_homology_record C S C1 t T T0 P Q A0 B0 D0 p0)) (@homology_record_object C S A1 B1 D1 p1 (@chain_pair_adjunction_homology_record C S C1 t T T0 P Q A1 B1 D1 p1)))
        (@chain_pair_adjunction_homology_map C S C1 t T T0 P Q A0 B0 D0 A1 B1 D1 p0 p1 m0)
        (@chain_pair_adjunction_homology_map C S C1 t T T0 P Q A0 B0 D0 A1 B1 D1 p0 p1 m1)));
