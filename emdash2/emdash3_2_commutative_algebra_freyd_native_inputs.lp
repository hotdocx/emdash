/* Direct native Freyd input before any kernel/cokernel selection.
   The known OneCat, preadditive and terminal-zero data are filled here. */
require open emdash.emdash3_2_commutative_algebra_freyd_chain_pair_data;
require open emdash.emdash3_2_commutative_algebra_freyd_zero_cones;
require open emdash.emdash3_2_one_cat_chain_pair_inputs;

// Raw morphisms and their original agreement form the native input directly.
symbol freyd_raw_chain_native_cone [R : τ CommRing]
  [A B D : τ (@CommRingPresentation R)]
  (e : τ (@CommRingPresentationMorphism R A B))
  (d : τ (@CommRingPresentationMorphism R B D))
  (chain : τ (@CommRingFreydChainPair R A B D e d))
  : τ (Obj (@ZeroArrowCone_cat (@CommRingFreydPresentation_cat R)
      (@comm_ring_zero_presentation R) (@comm_ring_freyd_terminal_zero R)))
≔ @chain_pair_native_cone (@CommRingFreydPresentation_cat R)
    (@comm_ring_freyd_preadditive R) (@comm_ring_freyd_cat_is_one_cat R)
    (@comm_ring_zero_presentation R) (@comm_ring_freyd_terminal_zero R)
    A B D (@freyd_raw_chain_pair_generic R A B D e d chain);
