/* All three actual raw components survive the formal/native bridge. */
require open emdash.emdash3_2_commutative_algebra_freyd_zero_cone_maps;

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
  @computational_chain_pair_map_next (@CommRingFreydPresentation_cat R) (@comm_ring_freyd_preadditive R)
    S2 S1 S0 T2 T1 T0 (@freyd_raw_chain_pair_generic R S2 S1 S0 sdNext sd chainS) (@freyd_raw_chain_pair_generic R T2 T1 T0 tdNext td chainT) (@freyd_raw_chain_map_generic R S2 S1 S0 T2 T1 T0 sdNext sd tdNext td f2 f1 f0 chainS chainT m)
  ≡ @comm_ring_freyd_hom_class R S2 T2 f2;

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
  @computational_chain_pair_map_middle (@CommRingFreydPresentation_cat R) (@comm_ring_freyd_preadditive R)
    S2 S1 S0 T2 T1 T0 (@freyd_raw_chain_pair_generic R S2 S1 S0 sdNext sd chainS) (@freyd_raw_chain_pair_generic R T2 T1 T0 tdNext td chainT) (@freyd_raw_chain_map_generic R S2 S1 S0 T2 T1 T0 sdNext sd tdNext td f2 f1 f0 chainS chainT m)
  ≡ @comm_ring_freyd_hom_class R S1 T1 f1;

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
  @computational_chain_pair_map_prev (@CommRingFreydPresentation_cat R) (@comm_ring_freyd_preadditive R)
    S2 S1 S0 T2 T1 T0 (@freyd_raw_chain_pair_generic R S2 S1 S0 sdNext sd chainS) (@freyd_raw_chain_pair_generic R T2 T1 T0 tdNext td chainT) (@freyd_raw_chain_map_generic R S2 S1 S0 T2 T1 T0 sdNext sd tdNext td f2 f1 f0 chainS chainT m)
  ≡ @comm_ring_freyd_hom_class R S0 T0 f0;

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
  (m : τ (@CommRingFreydHomologyChainMap R S2 S1 S0 T2 T1 T0 sdNext sd tdNext td f2 f1 f0)) [W : τ (@HasComputationalKernels (@CommRingFreydPresentation_cat R) (@comm_ring_freyd_preadditive R))]
  (P : τ (@KernelPresentation (@CommRingFreydPresentation_cat R) (@comm_ring_freyd_preadditive R) (@comm_ring_zero_presentation R) (@comm_ring_freyd_terminal_zero R) W)) ⊢
  @fapp1_fapp0 (@ZeroArrowCone_cat (@CommRingFreydPresentation_cat R) (@comm_ring_zero_presentation R) (@comm_ring_freyd_terminal_zero R)) (@CommRingFreydPresentation_cat R)
    (@zero_arrow_cone_first_func (@CommRingFreydPresentation_cat R) (@comm_ring_zero_presentation R) (@comm_ring_freyd_terminal_zero R))
    (@freyd_raw_chain_zero_cone R W P S2 S1 S0 sdNext sd chainS) (@freyd_raw_chain_zero_cone R W P T2 T1 T0 tdNext td chainT) (@freyd_raw_chain_zero_cone_map R W P S2 S1 S0 T2 T1 T0 sdNext sd tdNext td f2 f1 f0 chainS chainT m)
  ≡ @comm_ring_freyd_hom_class R S2 T2 f2;

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
  (m : τ (@CommRingFreydHomologyChainMap R S2 S1 S0 T2 T1 T0 sdNext sd tdNext td f2 f1 f0)) [W : τ (@HasComputationalKernels (@CommRingFreydPresentation_cat R) (@comm_ring_freyd_preadditive R))]
  (P : τ (@KernelPresentation (@CommRingFreydPresentation_cat R) (@comm_ring_freyd_preadditive R) (@comm_ring_zero_presentation R) (@comm_ring_freyd_terminal_zero R) W)) ⊢
  @tapp0_fapp0 WalkingArrow_cat (@CommRingFreydPresentation_cat R) _ _ walking_arrow_src
    (@fapp1_fapp0 (@ZeroArrowCone_cat (@CommRingFreydPresentation_cat R) (@comm_ring_zero_presentation R) (@comm_ring_freyd_terminal_zero R)) (Functor_cat WalkingArrow_cat (@CommRingFreydPresentation_cat R))
      (@zero_arrow_cone_diagram_func (@CommRingFreydPresentation_cat R) (@comm_ring_zero_presentation R) (@comm_ring_freyd_terminal_zero R))
      (@freyd_raw_chain_zero_cone R W P S2 S1 S0 sdNext sd chainS) (@freyd_raw_chain_zero_cone R W P T2 T1 T0 tdNext td chainT) (@freyd_raw_chain_zero_cone_map R W P S2 S1 S0 T2 T1 T0 sdNext sd tdNext td f2 f1 f0 chainS chainT m))
  ≡ @comm_ring_freyd_hom_class R S1 T1 f1;

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
  (m : τ (@CommRingFreydHomologyChainMap R S2 S1 S0 T2 T1 T0 sdNext sd tdNext td f2 f1 f0)) [W : τ (@HasComputationalKernels (@CommRingFreydPresentation_cat R) (@comm_ring_freyd_preadditive R))]
  (P : τ (@KernelPresentation (@CommRingFreydPresentation_cat R) (@comm_ring_freyd_preadditive R) (@comm_ring_zero_presentation R) (@comm_ring_freyd_terminal_zero R) W)) ⊢
  @tapp0_fapp0 WalkingArrow_cat (@CommRingFreydPresentation_cat R) _ _ walking_arrow_tgt
    (@fapp1_fapp0 (@ZeroArrowCone_cat (@CommRingFreydPresentation_cat R) (@comm_ring_zero_presentation R) (@comm_ring_freyd_terminal_zero R)) (Functor_cat WalkingArrow_cat (@CommRingFreydPresentation_cat R))
      (@zero_arrow_cone_diagram_func (@CommRingFreydPresentation_cat R) (@comm_ring_zero_presentation R) (@comm_ring_freyd_terminal_zero R))
      (@freyd_raw_chain_zero_cone R W P S2 S1 S0 sdNext sd chainS) (@freyd_raw_chain_zero_cone R W P T2 T1 T0 tdNext td chainT) (@freyd_raw_chain_zero_cone_map R W P S2 S1 S0 T2 T1 T0 sdNext sd tdNext td f2 f1 f0 chainS chainT m))
  ≡ @comm_ring_freyd_hom_class R S0 T0 f0;

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
  (m : τ (@CommRingFreydHomologyChainMap R S2 S1 S0 T2 T1 T0 sdNext sd tdNext td f2 f1 f0))
  [W : τ (@HasComputationalKernels (@CommRingFreydPresentation_cat R) (@comm_ring_freyd_preadditive R))]
  (P : τ (@KernelPresentation (@CommRingFreydPresentation_cat R) (@comm_ring_freyd_preadditive R) (@comm_ring_zero_presentation R) (@comm_ring_freyd_terminal_zero R) W))
  (Z : τ (@TerminalObject (Op_cat (@CommRingFreydPresentation_cat R)) (@comm_ring_zero_presentation R)))
  (V : τ (@HasComputationalCokernels (@CommRingFreydPresentation_cat R) (@comm_ring_freyd_preadditive R)))
  (Q : τ (@CokernelPresentation (@CommRingFreydPresentation_cat R) (@comm_ring_freyd_preadditive R) (@comm_ring_zero_presentation R) Z V)) ⊢
  @fapp1_fapp0 (@ZeroArrowCone_cat (@CommRingFreydPresentation_cat R) (@comm_ring_zero_presentation R) (@comm_ring_freyd_terminal_zero R)) (@CommRingFreydPresentation_cat R) (@freyd_zero_cone_homology_func R Z W V P Q) (@freyd_raw_chain_zero_cone R W P S2 S1 S0 sdNext sd chainS) (@freyd_raw_chain_zero_cone R W P T2 T1 T0 tdNext td chainT) (@freyd_raw_chain_zero_cone_map R W P S2 S1 S0 T2 T1 T0 sdNext sd tdNext td f2 f1 f0 chainS chainT m)
  : τ (Hom (@CommRingFreydPresentation_cat R) (@fapp0 (@ZeroArrowCone_cat (@CommRingFreydPresentation_cat R) (@comm_ring_zero_presentation R) (@comm_ring_freyd_terminal_zero R)) (@CommRingFreydPresentation_cat R) (@freyd_zero_cone_homology_func R Z W V P Q) (@freyd_raw_chain_zero_cone R W P S2 S1 S0 sdNext sd chainS))
      (@fapp0 (@ZeroArrowCone_cat (@CommRingFreydPresentation_cat R) (@comm_ring_zero_presentation R) (@comm_ring_freyd_terminal_zero R)) (@CommRingFreydPresentation_cat R) (@freyd_zero_cone_homology_func R Z W V P Q) (@freyd_raw_chain_zero_cone R W P T2 T1 T0 tdNext td chainT)));
