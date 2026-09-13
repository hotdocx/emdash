/* Whole H action and original record endpoints for raw Freyd maps. */
require open emdash.emdash3_2_commutative_algebra_freyd_adjunction_homology_maps;
require open emdash.emdash3_2_commutative_algebra_freyd_native_maps;
require open emdash.emdash3_2_commutative_algebra_freyd_adjunction_homology;

// This is exactly the original whole H action at the direct native map.
assert [R : τ CommRing]
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
  (m : τ (@CommRingFreydHomologyChainMap R S2 S1 S0 T2 T1 T0 sdNext sd tdNext td f2 f1 f0)) ⊢
  @freyd_raw_chain_adjunction_homology_map R Z P Q S2 S1 S0 T2 T1 T0 sdNext sd tdNext td f2 f1 f0 chainS chainT m
  ≡ @fapp1_fapp0 (@ZeroArrowCone_cat (@CommRingFreydPresentation_cat R) (@comm_ring_zero_presentation R) (@comm_ring_freyd_terminal_zero R)) (@CommRingFreydPresentation_cat R) (@freyd_zero_cone_adjunction_homology_func R Z P Q) (@freyd_raw_chain_native_cone R S2 S1 S0 sdNext sd chainS) (@freyd_raw_chain_native_cone R T2 T1 T0 tdNext td chainT) (@freyd_raw_chain_native_map R S2 S1 S0 T2 T1 T0 sdNext sd tdNext td f2 f1 f0 chainS chainT m);

// The endpoints are the retained original-input records.
assert [R : τ CommRing]
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
  (m : τ (@CommRingFreydHomologyChainMap R S2 S1 S0 T2 T1 T0 sdNext sd tdNext td f2 f1 f0)) ⊢
  @freyd_raw_chain_adjunction_homology_map R Z P Q S2 S1 S0 T2 T1 T0 sdNext sd tdNext td f2 f1 f0 chainS chainT m
  : τ (Hom (@CommRingFreydPresentation_cat R) (@homology_record_object (@CommRingFreydPresentation_cat R) (@comm_ring_freyd_preadditive R) S2 S1 S0 (@freyd_raw_chain_pair_generic R S2 S1 S0 sdNext sd chainS) (@freyd_raw_chain_adjunction_homology_record R Z P Q S2 S1 S0 sdNext sd chainS)) (@homology_record_object (@CommRingFreydPresentation_cat R) (@comm_ring_freyd_preadditive R) T2 T1 T0 (@freyd_raw_chain_pair_generic R T2 T1 T0 tdNext td chainT) (@freyd_raw_chain_adjunction_homology_record R Z P Q T2 T1 T0 tdNext td chainT)));

// Whole action in the raw-agreement parameter has the same record endpoints.
assert [R : τ CommRing]
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
  ⊢ @freyd_raw_chain_adjunction_homology_map_func R Z P Q S2 S1 S0 T2 T1 T0 sdNext sd tdNext td f2 f1 f0 chainS chainT
  : τ (Functor (Path_cat (@CommRingFreydHomologyChainMap R S2 S1 S0 T2 T1 T0 sdNext sd tdNext td f2 f1 f0)) (Hom_cat (@CommRingFreydPresentation_cat R) (@homology_record_object (@CommRingFreydPresentation_cat R) (@comm_ring_freyd_preadditive R) S2 S1 S0 (@freyd_raw_chain_pair_generic R S2 S1 S0 sdNext sd chainS) (@freyd_raw_chain_adjunction_homology_record R Z P Q S2 S1 S0 sdNext sd chainS)) (@homology_record_object (@CommRingFreydPresentation_cat R) (@comm_ring_freyd_preadditive R) T2 T1 T0 (@freyd_raw_chain_pair_generic R T2 T1 T0 tdNext td chainT) (@freyd_raw_chain_adjunction_homology_record R Z P Q T2 T1 T0 tdNext td chainT))));

// A further whole Hom action remains available.
assert [R : τ CommRing]
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
  (m0 m1 : τ (@CommRingFreydHomologyChainMap R S2 S1 S0 T2 T1 T0 sdNext sd tdNext td f2 f1 f0)) ⊢
  @fapp1_func _ _ (@freyd_raw_chain_adjunction_homology_map_func R Z P Q S2 S1 S0 T2 T1 T0 sdNext sd tdNext td f2 f1 f0 chainS chainT) m0 m1
  : τ (Functor (Hom_cat (Path_cat (@CommRingFreydHomologyChainMap R S2 S1 S0 T2 T1 T0 sdNext sd tdNext td f2 f1 f0)) m0 m1)
      (Hom_cat (Hom_cat (@CommRingFreydPresentation_cat R) (@homology_record_object (@CommRingFreydPresentation_cat R) (@comm_ring_freyd_preadditive R) S2 S1 S0 (@freyd_raw_chain_pair_generic R S2 S1 S0 sdNext sd chainS) (@freyd_raw_chain_adjunction_homology_record R Z P Q S2 S1 S0 sdNext sd chainS)) (@homology_record_object (@CommRingFreydPresentation_cat R) (@comm_ring_freyd_preadditive R) T2 T1 T0 (@freyd_raw_chain_pair_generic R T2 T1 T0 tdNext td chainT) (@freyd_raw_chain_adjunction_homology_record R Z P Q T2 T1 T0 tdNext td chainT)))
        (@freyd_raw_chain_adjunction_homology_map R Z P Q S2 S1 S0 T2 T1 T0 sdNext sd tdNext td f2 f1 f0 chainS chainT m0)
        (@freyd_raw_chain_adjunction_homology_map R Z P Q S2 S1 S0 T2 T1 T0 sdNext sd tdNext td f2 f1 f0 chainS chainT m1)));
