/* Whole homology and its original-pair record for raw Freyd inputs.
   P/Q are explicit whole model structures; raw agreements do not create
   those structures. All operations specialize existing generic owners. */
require open emdash.emdash3_2_commutative_algebra_freyd_native_inputs;
require open emdash.emdash3_2_one_cat_chain_pair_homology_records;

// The whole functor uses explicit P/Q, with the local categorical data filled.
symbol freyd_zero_cone_adjunction_homology_func [R : τ CommRing]
  [T0 : τ (@TerminalObject (Op_cat (@CommRingFreydPresentation_cat R))
    (@comm_ring_zero_presentation R))]
  (P : τ (@KernelAdjunctionStructure (@CommRingFreydPresentation_cat R)
    (@comm_ring_freyd_preadditive R) (@comm_ring_zero_presentation R)
    (@comm_ring_freyd_terminal_zero R)))
  (Q : τ (@CokernelAdjunctionStructure (@CommRingFreydPresentation_cat R)
    (@comm_ring_freyd_preadditive R) (@comm_ring_zero_presentation R) T0))
  : τ (Functor
      (@ZeroArrowCone_cat (@CommRingFreydPresentation_cat R)
        (@comm_ring_zero_presentation R) (@comm_ring_freyd_terminal_zero R))
      (@CommRingFreydPresentation_cat R))
≔ @zero_arrow_cone_adjunction_homology_func (@CommRingFreydPresentation_cat R)
    (@comm_ring_freyd_preadditive R) (@comm_ring_freyd_cat_is_one_cat R)
    (@comm_ring_zero_presentation R) (@comm_ring_freyd_terminal_zero R)
    T0 P Q;

// The ordinary record observes the same original raw pair and whole H.
symbol freyd_raw_chain_adjunction_homology_record [R : τ CommRing]
  [T0 : τ (@TerminalObject (Op_cat (@CommRingFreydPresentation_cat R)) (@comm_ring_zero_presentation R))]
  (P : τ (@KernelAdjunctionStructure (@CommRingFreydPresentation_cat R)
    (@comm_ring_freyd_preadditive R) (@comm_ring_zero_presentation R) (@comm_ring_freyd_terminal_zero R)))
  (Q : τ (@CokernelAdjunctionStructure (@CommRingFreydPresentation_cat R)
    (@comm_ring_freyd_preadditive R) (@comm_ring_zero_presentation R) T0))
  [A B D : τ (@CommRingPresentation R)]
  (e : τ (@CommRingPresentationMorphism R A B))
  (d : τ (@CommRingPresentationMorphism R B D))
  (chain : τ (@CommRingFreydChainPair R A B D e d))
  : τ (@HomologyRecord (@CommRingFreydPresentation_cat R)
      (@comm_ring_freyd_preadditive R) A B D
      (@freyd_raw_chain_pair_generic R A B D e d chain))
≔ @chain_pair_adjunction_homology_record (@CommRingFreydPresentation_cat R)
    (@comm_ring_freyd_preadditive R) (@comm_ring_freyd_cat_is_one_cat R)
    (@comm_ring_zero_presentation R) (@comm_ring_freyd_terminal_zero R) T0 P Q
    A B D (@freyd_raw_chain_pair_generic R A B D e d chain);
