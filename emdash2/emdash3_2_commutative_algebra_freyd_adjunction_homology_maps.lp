/* Whole H-map action for the original Freyd raw-map data.
   Existing generic H Hom-action is composed with the raw-agreement functor.
   P/Q remain whole structure; no per-map coherence premise is supplied. */
require open emdash.emdash3_2_commutative_algebra_freyd_chain_map_data;
require open emdash.emdash3_2_commutative_algebra_freyd_native_inputs;
require open emdash.emdash3_2_one_cat_chain_pair_homology_maps;

// The existing whole H-map action after raw-agreement conversion.
symbol freyd_raw_chain_adjunction_homology_map_func [R : τ CommRing]
  [Z : τ (@TerminalObject (Op_cat (@CommRingFreydPresentation_cat R)) (@comm_ring_zero_presentation R))]
  (P : τ (@KernelAdjunctionStructure (@CommRingFreydPresentation_cat R) (@comm_ring_freyd_preadditive R) (@comm_ring_zero_presentation R) (@comm_ring_freyd_terminal_zero R)))
  (Q : τ (@CokernelAdjunctionStructure (@CommRingFreydPresentation_cat R) (@comm_ring_freyd_preadditive R) (@comm_ring_zero_presentation R) Z))
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
  : τ (Functor (Path_cat (@CommRingFreydHomologyChainMap R S2 S1 S0 T2 T1 T0 sdNext sd tdNext td f2 f1 f0)) (Hom_cat (@CommRingFreydPresentation_cat R) (@fapp0 (@ZeroArrowCone_cat (@CommRingFreydPresentation_cat R) (@comm_ring_zero_presentation R) (@comm_ring_freyd_terminal_zero R)) (@CommRingFreydPresentation_cat R) (@zero_arrow_cone_adjunction_homology_func (@CommRingFreydPresentation_cat R) (@comm_ring_freyd_preadditive R) (@comm_ring_freyd_cat_is_one_cat R) (@comm_ring_zero_presentation R) (@comm_ring_freyd_terminal_zero R) Z P Q) (@freyd_raw_chain_native_cone R S2 S1 S0 sdNext sd chainS)) (@fapp0 (@ZeroArrowCone_cat (@CommRingFreydPresentation_cat R) (@comm_ring_zero_presentation R) (@comm_ring_freyd_terminal_zero R)) (@CommRingFreydPresentation_cat R) (@zero_arrow_cone_adjunction_homology_func (@CommRingFreydPresentation_cat R) (@comm_ring_freyd_preadditive R) (@comm_ring_freyd_cat_is_one_cat R) (@comm_ring_zero_presentation R) (@comm_ring_freyd_terminal_zero R) Z P Q) (@freyd_raw_chain_native_cone R T2 T1 T0 tdNext td chainT))))
≔ @comp_cat_fapp0 (Path_cat (@CommRingFreydHomologyChainMap R S2 S1 S0 T2 T1 T0 sdNext sd tdNext td f2 f1 f0)) (Path_cat (@ComputationalChainPairMap (@CommRingFreydPresentation_cat R) (@comm_ring_freyd_preadditive R) S2 S1 S0 T2 T1 T0 (@freyd_raw_chain_pair_generic R S2 S1 S0 sdNext sd chainS) (@freyd_raw_chain_pair_generic R T2 T1 T0 tdNext td chainT))) (Hom_cat (@CommRingFreydPresentation_cat R) (@fapp0 (@ZeroArrowCone_cat (@CommRingFreydPresentation_cat R) (@comm_ring_zero_presentation R) (@comm_ring_freyd_terminal_zero R)) (@CommRingFreydPresentation_cat R) (@zero_arrow_cone_adjunction_homology_func (@CommRingFreydPresentation_cat R) (@comm_ring_freyd_preadditive R) (@comm_ring_freyd_cat_is_one_cat R) (@comm_ring_zero_presentation R) (@comm_ring_freyd_terminal_zero R) Z P Q) (@freyd_raw_chain_native_cone R S2 S1 S0 sdNext sd chainS)) (@fapp0 (@ZeroArrowCone_cat (@CommRingFreydPresentation_cat R) (@comm_ring_zero_presentation R) (@comm_ring_freyd_terminal_zero R)) (@CommRingFreydPresentation_cat R) (@zero_arrow_cone_adjunction_homology_func (@CommRingFreydPresentation_cat R) (@comm_ring_freyd_preadditive R) (@comm_ring_freyd_cat_is_one_cat R) (@comm_ring_zero_presentation R) (@comm_ring_freyd_terminal_zero R) Z P Q) (@freyd_raw_chain_native_cone R T2 T1 T0 tdNext td chainT)))
    (@chain_pair_adjunction_homology_map_func (@CommRingFreydPresentation_cat R) (@comm_ring_freyd_preadditive R) (@comm_ring_freyd_cat_is_one_cat R) (@comm_ring_zero_presentation R) (@comm_ring_freyd_terminal_zero R) Z P Q S2 S1 S0 T2 T1 T0 (@freyd_raw_chain_pair_generic R S2 S1 S0 sdNext sd chainS) (@freyd_raw_chain_pair_generic R T2 T1 T0 tdNext td chainT))
    (@freyd_raw_chain_map_path_func R S2 S1 S0 T2 T1 T0 sdNext sd tdNext td f2 f1 f0 chainS chainT);

// Point view; no separate homology map or coherence law is supplied.
symbol freyd_raw_chain_adjunction_homology_map [R : τ CommRing]
  [Z : τ (@TerminalObject (Op_cat (@CommRingFreydPresentation_cat R)) (@comm_ring_zero_presentation R))]
  (P : τ (@KernelAdjunctionStructure (@CommRingFreydPresentation_cat R) (@comm_ring_freyd_preadditive R) (@comm_ring_zero_presentation R) (@comm_ring_freyd_terminal_zero R)))
  (Q : τ (@CokernelAdjunctionStructure (@CommRingFreydPresentation_cat R) (@comm_ring_freyd_preadditive R) (@comm_ring_zero_presentation R) Z))
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
  : τ (Hom (@CommRingFreydPresentation_cat R) (@fapp0 (@ZeroArrowCone_cat (@CommRingFreydPresentation_cat R) (@comm_ring_zero_presentation R) (@comm_ring_freyd_terminal_zero R)) (@CommRingFreydPresentation_cat R) (@zero_arrow_cone_adjunction_homology_func (@CommRingFreydPresentation_cat R) (@comm_ring_freyd_preadditive R) (@comm_ring_freyd_cat_is_one_cat R) (@comm_ring_zero_presentation R) (@comm_ring_freyd_terminal_zero R) Z P Q) (@freyd_raw_chain_native_cone R S2 S1 S0 sdNext sd chainS)) (@fapp0 (@ZeroArrowCone_cat (@CommRingFreydPresentation_cat R) (@comm_ring_zero_presentation R) (@comm_ring_freyd_terminal_zero R)) (@CommRingFreydPresentation_cat R) (@zero_arrow_cone_adjunction_homology_func (@CommRingFreydPresentation_cat R) (@comm_ring_freyd_preadditive R) (@comm_ring_freyd_cat_is_one_cat R) (@comm_ring_zero_presentation R) (@comm_ring_freyd_terminal_zero R) Z P Q) (@freyd_raw_chain_native_cone R T2 T1 T0 tdNext td chainT)))
≔ @fapp0 (Path_cat (@CommRingFreydHomologyChainMap R S2 S1 S0 T2 T1 T0 sdNext sd tdNext td f2 f1 f0)) (Hom_cat (@CommRingFreydPresentation_cat R) (@fapp0 (@ZeroArrowCone_cat (@CommRingFreydPresentation_cat R) (@comm_ring_zero_presentation R) (@comm_ring_freyd_terminal_zero R)) (@CommRingFreydPresentation_cat R) (@zero_arrow_cone_adjunction_homology_func (@CommRingFreydPresentation_cat R) (@comm_ring_freyd_preadditive R) (@comm_ring_freyd_cat_is_one_cat R) (@comm_ring_zero_presentation R) (@comm_ring_freyd_terminal_zero R) Z P Q) (@freyd_raw_chain_native_cone R S2 S1 S0 sdNext sd chainS)) (@fapp0 (@ZeroArrowCone_cat (@CommRingFreydPresentation_cat R) (@comm_ring_zero_presentation R) (@comm_ring_freyd_terminal_zero R)) (@CommRingFreydPresentation_cat R) (@zero_arrow_cone_adjunction_homology_func (@CommRingFreydPresentation_cat R) (@comm_ring_freyd_preadditive R) (@comm_ring_freyd_cat_is_one_cat R) (@comm_ring_zero_presentation R) (@comm_ring_freyd_terminal_zero R) Z P Q) (@freyd_raw_chain_native_cone R T2 T1 T0 tdNext td chainT)))
    (@freyd_raw_chain_adjunction_homology_map_func R Z P Q S2 S1 S0 T2 T1 T0 sdNext sd tdNext td f2 f1 f0 chainS chainT) m;
