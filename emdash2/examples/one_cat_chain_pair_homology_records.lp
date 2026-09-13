/* Whole H and its actual boundary at ORIGINAL raw pair indices. */
require open emdash.emdash3_2_one_cat_chain_pair_homology_records;

// Cycles are K at the original outgoing diagram.
assert [C : Cat] [S : τ (@PreadditiveCategory C)]
  (C1 : τ (IsNCat (cat_succ cat_zero) C))
  [t : τ (Obj C)] [T : τ (@TerminalObject C t)] [T0 : τ (@TerminalObject (Op_cat C) t)]
  (P : τ (@KernelAdjunctionStructure C S t T)) (Q : τ (@CokernelAdjunctionStructure C S t T0))
  [A B D : τ (Obj C)] (pair : τ (@ComputationalChainPair C S A B D))
  ⊢
  @homology_record_cycle_object C S A B D pair (@chain_pair_adjunction_homology_record C S C1 t T T0 P Q A B D pair)
  ≡ @fapp0 (Functor_cat WalkingArrow_cat C) C (@kernel_adjunction_func C S t T P) (@chain_pair_outgoing_diagram C S A B D pair);

// The actual β belongs to the original native input.
assert [C : Cat] [S : τ (@PreadditiveCategory C)]
  (C1 : τ (IsNCat (cat_succ cat_zero) C))
  [t : τ (Obj C)] [T : τ (@TerminalObject C t)] [T0 : τ (@TerminalObject (Op_cat C) t)]
  (P : τ (@KernelAdjunctionStructure C S t T)) (Q : τ (@CokernelAdjunctionStructure C S t T0))
  [A B D : τ (Obj C)] (pair : τ (@ComputationalChainPair C S A B D))
  ⊢
  @homology_record_boundary C S A B D pair (@chain_pair_adjunction_homology_record C S C1 t T T0 P Q A B D pair)
  ≡ @tapp0_fapp0 (@ZeroArrowCone_cat C t T) C _ _ (@chain_pair_native_cone C S C1 t T A B D pair) (@kernel_adjunction_family_boundary_transf (@ZeroArrowCone_cat C t T) C S t T P (@zero_arrow_cone_first_func C t T) (@zero_arrow_cone_diagram_func C t T) (@zero_arrow_cone_universal_transf C C1 t T));

// The record object is the whole H at the input formed before selection.
assert [C : Cat] [S : τ (@PreadditiveCategory C)]
  (C1 : τ (IsNCat (cat_succ cat_zero) C))
  [t : τ (Obj C)] [T : τ (@TerminalObject C t)] [T0 : τ (@TerminalObject (Op_cat C) t)]
  (P : τ (@KernelAdjunctionStructure C S t T)) (Q : τ (@CokernelAdjunctionStructure C S t T0))
  [A B D : τ (Obj C)] (pair : τ (@ComputationalChainPair C S A B D))
  ⊢
  @homology_record_object C S A B D pair (@chain_pair_adjunction_homology_record C S C1 t T T0 P Q A B D pair)
  ≡ @fapp0 (@ZeroArrowCone_cat C t T) C (@zero_arrow_cone_adjunction_homology_func C S C1 t T T0 P Q) (@chain_pair_native_cone C S C1 t T A B D pair);

// The boundary reconstructs the original incoming differential.
assert [C : Cat] [S : τ (@PreadditiveCategory C)]
  (C1 : τ (IsNCat (cat_succ cat_zero) C))
  [t : τ (Obj C)] [T : τ (@TerminalObject C t)] [T0 : τ (@TerminalObject (Op_cat C) t)]
  (P : τ (@KernelAdjunctionStructure C S t T)) (Q : τ (@CokernelAdjunctionStructure C S t T0))
  [A B D : τ (Obj C)] (pair : τ (@ComputationalChainPair C S A B D))
  ⊢
  @homology_record_boundary_path C S A B D pair (@chain_pair_adjunction_homology_record C S C1 t T T0 P Q A B D pair)
  : τ (@= (Hom C A B)
    (@comp_fapp0 C A (@fapp0 (Functor_cat WalkingArrow_cat C) C (@kernel_adjunction_func C S t T P) (@chain_pair_outgoing_diagram C S A B D pair)) B
      (@tapp0_fapp0 (Functor_cat WalkingArrow_cat C) C _ _ (@chain_pair_outgoing_diagram C S A B D pair) (@kernel_adjunction_inclusion C S t T P)) (@homology_record_boundary C S A B D pair (@chain_pair_adjunction_homology_record C S C1 t T T0 P Q A B D pair)))
    (@computational_chain_pair_dnext C S A B D pair));

// Native input arrows act by the existing whole H at both record endpoints.
assert [C : Cat] [S : τ (@PreadditiveCategory C)]
  (C1 : τ (IsNCat (cat_succ cat_zero) C))
  [t : τ (Obj C)] [T : τ (@TerminalObject C t)] [T0 : τ (@TerminalObject (Op_cat C) t)]
  (P : τ (@KernelAdjunctionStructure C S t T)) (Q : τ (@CokernelAdjunctionStructure C S t T0))
  [A B D : τ (Obj C)] (pair : τ (@ComputationalChainPair C S A B D))
  [A1 B1 D1 : τ (Obj C)] (pair1 : τ (@ComputationalChainPair C S A1 B1 D1))
  (g : τ (Hom (@ZeroArrowCone_cat C t T) (@chain_pair_native_cone C S C1 t T A B D pair) (@chain_pair_native_cone C S C1 t T A1 B1 D1 pair1))) ⊢
  @fapp1_fapp0 (@ZeroArrowCone_cat C t T) C (@zero_arrow_cone_adjunction_homology_func C S C1 t T T0 P Q) (@chain_pair_native_cone C S C1 t T A B D pair) (@chain_pair_native_cone C S C1 t T A1 B1 D1 pair1) g
  : τ (Hom C (@homology_record_object C S A B D pair (@chain_pair_adjunction_homology_record C S C1 t T T0 P Q A B D pair)) (@homology_record_object C S A1 B1 D1 pair1 (@chain_pair_adjunction_homology_record C S C1 t T T0 P Q A1 B1 D1 pair1)));
