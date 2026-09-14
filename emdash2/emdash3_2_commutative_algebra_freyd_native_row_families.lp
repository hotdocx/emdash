/* Raw rows and their existing maps enter as constant parameter families.
   Weakening supplies all parameter action; no per-object coherence is requested. */
require open emdash.emdash3_2_commutative_algebra_freyd_native_maps;

// The row exists before kernel/cokernel selection.
symbol freyd_raw_native_row_family [K : Cat] [R : τ CommRing]
  [A B D : τ (@CommRingPresentation R)]
  (e : τ (@CommRingPresentationMorphism R A B))
  (d : τ (@CommRingPresentationMorphism R B D))
  (chain : τ (@CommRingFreydChainPair R A B D e d))
  : τ (Functor K (@ZeroArrowCone_cat (@CommRingFreydPresentation_cat R) (@comm_ring_zero_presentation R)
    (@comm_ring_freyd_terminal_zero R)))
≔ @Const_func K (@ZeroArrowCone_cat (@CommRingFreydPresentation_cat R) (@comm_ring_zero_presentation R)
    (@comm_ring_freyd_terminal_zero R)) (@freyd_raw_chain_native_cone R A B D e d chain);

// Whole action in the existing raw map-agreement parameter.
symbol freyd_raw_native_row_map_func [K : Cat] [R : τ CommRing]
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
  : τ (Functor (Path_cat (@CommRingFreydHomologyChainMap R S2 S1 S0 T2 T1 T0 sdNext sd tdNext td f2 f1 f0))
    (@Transf_cat K (@ZeroArrowCone_cat (@CommRingFreydPresentation_cat R) (@comm_ring_zero_presentation R)
    (@comm_ring_freyd_terminal_zero R)) (@freyd_raw_native_row_family K R S2 S1 S0 sdNext sd chainS)
    (@freyd_raw_native_row_family K R T2 T1 T0 tdNext td chainT)))
≔ @comp_cat_fapp0 (Path_cat (@CommRingFreydHomologyChainMap R S2 S1 S0 T2 T1 T0 sdNext sd tdNext td f2 f1
    f0)) (Hom_cat (@ZeroArrowCone_cat (@CommRingFreydPresentation_cat R) (@comm_ring_zero_presentation R)
    (@comm_ring_freyd_terminal_zero R)) (@freyd_raw_chain_native_cone R S2 S1 S0 sdNext sd chainS)
    (@freyd_raw_chain_native_cone R T2 T1 T0 tdNext td chainT)) (@Transf_cat K (@ZeroArrowCone_cat
    (@CommRingFreydPresentation_cat R) (@comm_ring_zero_presentation R) (@comm_ring_freyd_terminal_zero R))
    (@freyd_raw_native_row_family K R S2 S1 S0 sdNext sd chainS) (@freyd_raw_native_row_family K R T2 T1 T0
    tdNext td chainT)) (@Const_transf_func K (@ZeroArrowCone_cat (@CommRingFreydPresentation_cat R)
    (@comm_ring_zero_presentation R) (@comm_ring_freyd_terminal_zero R)) (@freyd_raw_chain_native_cone R S2
    S1 S0 sdNext sd chainS) (@freyd_raw_chain_native_cone R T2 T1 T0 tdNext td chainT))
    (@freyd_raw_chain_native_map_func R S2 S1 S0 T2 T1 T0 sdNext sd tdNext td f2 f1 f0 chainS chainT);

// Point view of that same whole action; components are the original native map.
symbol freyd_raw_native_row_map [K : Cat] [R : τ CommRing]
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
  : τ (Obj (@Transf_cat K (@ZeroArrowCone_cat (@CommRingFreydPresentation_cat R)
    (@comm_ring_zero_presentation R) (@comm_ring_freyd_terminal_zero R)) (@freyd_raw_native_row_family K R
    S2 S1 S0 sdNext sd chainS) (@freyd_raw_native_row_family K R T2 T1 T0 tdNext td chainT)))
≔ @fapp0 (Path_cat (@CommRingFreydHomologyChainMap R S2 S1 S0 T2 T1 T0 sdNext sd tdNext td f2 f1 f0))
    (@Transf_cat K (@ZeroArrowCone_cat (@CommRingFreydPresentation_cat R) (@comm_ring_zero_presentation R)
    (@comm_ring_freyd_terminal_zero R)) (@freyd_raw_native_row_family K R S2 S1 S0 sdNext sd chainS)
    (@freyd_raw_native_row_family K R T2 T1 T0 tdNext td chainT)) (@freyd_raw_native_row_map_func K R S2 S1
    S0 T2 T1 T0 sdNext sd tdNext td f2 f1 f0 chainS chainT) m;
