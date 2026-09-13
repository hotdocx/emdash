/* Original raw components are retained without kernel-presentation input. */
require open emdash.emdash3_2_commutative_algebra_freyd_native_maps;

// The original next raw morphism class is retained.
assert [R : τ CommRing]
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
  @fapp1_fapp0 (@ZeroArrowCone_cat (@CommRingFreydPresentation_cat R) (@comm_ring_zero_presentation R) (@comm_ring_freyd_terminal_zero R)) (@CommRingFreydPresentation_cat R) (@zero_arrow_cone_first_func (@CommRingFreydPresentation_cat R) (@comm_ring_zero_presentation R) (@comm_ring_freyd_terminal_zero R)) (@freyd_raw_chain_native_cone R S2 S1 S0 sdNext sd chainS) (@freyd_raw_chain_native_cone R T2 T1 T0 tdNext td chainT) (@freyd_raw_chain_native_map R S2 S1 S0 T2 T1 T0 sdNext sd tdNext td f2 f1 f0 chainS chainT m)
  ≡ @comm_ring_freyd_hom_class R S2 T2 f2;

// The original middle raw morphism class is retained.
assert [R : τ CommRing]
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
  @tapp0_fapp0 WalkingArrow_cat (@CommRingFreydPresentation_cat R) _ _ walking_arrow_src (@fapp1_fapp0 (@ZeroArrowCone_cat (@CommRingFreydPresentation_cat R) (@comm_ring_zero_presentation R) (@comm_ring_freyd_terminal_zero R)) (Functor_cat WalkingArrow_cat (@CommRingFreydPresentation_cat R)) (@zero_arrow_cone_diagram_func (@CommRingFreydPresentation_cat R) (@comm_ring_zero_presentation R) (@comm_ring_freyd_terminal_zero R)) (@freyd_raw_chain_native_cone R S2 S1 S0 sdNext sd chainS) (@freyd_raw_chain_native_cone R T2 T1 T0 tdNext td chainT) (@freyd_raw_chain_native_map R S2 S1 S0 T2 T1 T0 sdNext sd tdNext td f2 f1 f0 chainS chainT m))
  ≡ @comm_ring_freyd_hom_class R S1 T1 f1;

// The original previous raw morphism class is retained.
assert [R : τ CommRing]
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
  @tapp0_fapp0 WalkingArrow_cat (@CommRingFreydPresentation_cat R) _ _ walking_arrow_tgt (@fapp1_fapp0 (@ZeroArrowCone_cat (@CommRingFreydPresentation_cat R) (@comm_ring_zero_presentation R) (@comm_ring_freyd_terminal_zero R)) (Functor_cat WalkingArrow_cat (@CommRingFreydPresentation_cat R)) (@zero_arrow_cone_diagram_func (@CommRingFreydPresentation_cat R) (@comm_ring_zero_presentation R) (@comm_ring_freyd_terminal_zero R)) (@freyd_raw_chain_native_cone R S2 S1 S0 sdNext sd chainS) (@freyd_raw_chain_native_cone R T2 T1 T0 tdNext td chainT) (@freyd_raw_chain_native_map R S2 S1 S0 T2 T1 T0 sdNext sd tdNext td f2 f1 f0 chainS chainT m))
  ≡ @comm_ring_freyd_hom_class R S0 T0 f0;

// Whole raw-agreement action returns the same native map.
assert [R : τ CommRing]
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
  @fapp0 _ _ (@freyd_raw_chain_native_map_func R S2 S1 S0 T2 T1 T0 sdNext sd tdNext td f2 f1 f0 chainS chainT) m
  ≡ (@freyd_raw_chain_native_map R S2 S1 S0 T2 T1 T0 sdNext sd tdNext td f2 f1 f0 chainS chainT m);
