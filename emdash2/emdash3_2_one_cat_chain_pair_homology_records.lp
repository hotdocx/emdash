/* Whole-H record over the original raw pair.
   Input formation is independent of universality. Whole P/Q are applied
   afterwards, retaining the actual boundary and quotient diagram. */
require open emdash.emdash3_2_homology_records;
require open emdash.emdash3_2_homology_adjunction_record_data;
require open emdash.emdash3_2_one_cat_adjunction_records;
require open emdash.emdash3_2_one_cat_chain_pair_inputs;
require open emdash.emdash3_2_zero_arrow_cone_adjunction_homology;

// Observe the whole boundary-diagram family at the original native input.
symbol chain_pair_adjunction_boundary_diagram [C : Cat] [S : τ (@PreadditiveCategory C)]
  (C1 : τ (IsNCat (cat_succ cat_zero) C))
  [t : τ (Obj C)] [T : τ (@TerminalObject C t)]
  (P : τ (@KernelAdjunctionStructure C S t T))
  [A B D : τ (Obj C)] (pair : τ (@ComputationalChainPair C S A B D))
  : τ (Functor WalkingArrow_cat C)
≔ @fapp0 (@ZeroArrowCone_cat C t T) (Functor_cat WalkingArrow_cat C)
    (@kernel_adjunction_family_boundary_diagram_func (@ZeroArrowCone_cat C t T) C S t T P
      (@zero_arrow_cone_first_func C t T) (@zero_arrow_cone_diagram_func C t T)
      (@zero_arrow_cone_universal_transf C C1 t T))
    (@chain_pair_native_cone C S C1 t T A B D pair);

// Reuse the actual semantic factor at the original pair endpoints.
symbol chain_pair_adjunction_boundary_factor [C : Cat] [S : τ (@PreadditiveCategory C)]
  (C1 : τ (IsNCat (cat_succ cat_zero) C))
  [t : τ (Obj C)] [T : τ (@TerminalObject C t)]
  (P : τ (@KernelAdjunctionStructure C S t T))
  [A B D : τ (Obj C)] (pair : τ (@ComputationalChainPair C S A B D))
  : τ (@KernelFactorSpace C S B D (@computational_chain_pair_d C S A B D pair)
    (@fapp0 _ _ (@kernel_adjunction_func C S t T P) (@chain_pair_outgoing_diagram C S A B D pair)) (@tapp0_fapp0 _ _ _ _ (@chain_pair_outgoing_diagram C S A B D pair) (@kernel_adjunction_inclusion C S t T P)) A (@computational_chain_pair_cone C S A B D pair))
≔ @kernel_adjunction_semantic_boundary_factor C S t T P A
    (@chain_pair_outgoing_diagram C S A B D pair)
    (@chain_pair_native_transf C S C1 t T A B D pair);

// Ordinary universality with the original pair as a literal index.
symbol chain_pair_adjunction_homology_record [C : Cat] [S : τ (@PreadditiveCategory C)]
  (C1 : τ (IsNCat (cat_succ cat_zero) C))
  [t : τ (Obj C)] [T : τ (@TerminalObject C t)] [T0 : τ (@TerminalObject (Op_cat C) t)]
  (P : τ (@KernelAdjunctionStructure C S t T)) (Q : τ (@CokernelAdjunctionStructure C S t T0))
  [A B D : τ (Obj C)] (pair : τ (@ComputationalChainPair C S A B D))
  : τ (@HomologyRecord C S A B D pair)
≔ @homology_record_intro C S A B D pair
    (@kernel_adjunction_record C S C1 t T P (@chain_pair_outgoing_diagram C S A B D pair))
    (@chain_pair_adjunction_boundary_factor C S C1 t T P A B D pair)
    (@cokernel_adjunction_record C S C1 t T0 Q (@chain_pair_adjunction_boundary_diagram C S C1 t T P A B D pair));
