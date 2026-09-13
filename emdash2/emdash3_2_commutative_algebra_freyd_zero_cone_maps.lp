/* Existing raw-map agreements enter the original generic factor interface. */
require open emdash.emdash3_2_chain_pair_zero_cone_maps;
require open emdash.emdash3_2_commutative_algebra_freyd_zero_cone_inputs;
require open emdash.emdash3_2_commutative_algebra_freyd_functorial_homology;
require open emdash.emdash3_2_commutative_algebra_freyd_chain_map_data;

// The OneCat profile is filled internally. P still realizes the chosen W.
symbol freyd_raw_chain_zero_cone_map [R : τ CommRing]
  [W : τ (@HasComputationalKernels (@CommRingFreydPresentation_cat R) (@comm_ring_freyd_preadditive R))]
  (P : τ (@KernelPresentation (@CommRingFreydPresentation_cat R) (@comm_ring_freyd_preadditive R) (@comm_ring_zero_presentation R) (@comm_ring_freyd_terminal_zero R) W))
  [S2 S1 S0 T2 T1 T0 : τ (@CommRingPresentation R)]
  [sdNext : τ (@CommRingPresentationMorphism R S2 S1)]
  [sd : τ (@CommRingPresentationMorphism R S1 S0)]
  [tdNext : τ (@CommRingPresentationMorphism R T2 T1)]
  [td : τ (@CommRingPresentationMorphism R T1 T0)]
  [f2 : τ (@CommRingPresentationMorphism R S2 T2)]
  [f1 : τ (@CommRingPresentationMorphism R S1 T1)]
  [f0 : τ (@CommRingPresentationMorphism R S0 T0)]
  (chainS : τ (@CommRingFreydChainPair R S2 S1 S0 sdNext sd))
  (chainT : τ (@CommRingFreydChainPair R T2 T1 T0 tdNext td))
  (m : τ (@CommRingFreydHomologyChainMap R S2 S1 S0 T2 T1 T0 sdNext sd tdNext td f2 f1 f0))
  : τ (Hom (@ZeroArrowCone_cat (@CommRingFreydPresentation_cat R) (@comm_ring_zero_presentation R) (@comm_ring_freyd_terminal_zero R))
      (@freyd_raw_chain_zero_cone R W P S2 S1 S0 sdNext sd chainS)
      (@freyd_raw_chain_zero_cone R W P T2 T1 T0 tdNext td chainT))
≔ @chain_pair_zero_cone_map (@CommRingFreydPresentation_cat R) (@comm_ring_freyd_preadditive R) (@comm_ring_freyd_cat_is_one_cat R)
    (@comm_ring_zero_presentation R) (@comm_ring_freyd_terminal_zero R) W P
    S2 S1 S0 T2 T1 T0 (@freyd_raw_chain_pair_generic R S2 S1 S0 sdNext sd chainS) (@freyd_raw_chain_pair_generic R T2 T1 T0 tdNext td chainT) (@freyd_raw_chain_map_generic R S2 S1 S0 T2 T1 T0 sdNext sd tdNext td f2 f1 f0 chainS chainT m);
