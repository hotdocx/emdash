/* Existing raw-map agreements enter the original generic factor interface. */
require open emdash.emdash3_2_chain_pair_zero_cone_maps;
require open emdash.emdash3_2_commutative_algebra_freyd_zero_cone_inputs;
require open emdash.emdash3_2_commutative_algebra_freyd_functorial_homology;

// Generic composition owners on both sides of one existing raw agreement.
symbol freyd_raw_composite_agreement_path [R : τ CommRing]
  [A B C D : τ (@CommRingPresentation R)]
  (f : τ (@CommRingPresentationMorphism R A B))
  (g : τ (@CommRingPresentationMorphism R B D))
  (h : τ (@CommRingPresentationMorphism R A C))
  (k : τ (@CommRingPresentationMorphism R C D))
  (p : τ (@CommRingPresentationMorphismAgreement R A D
    (@comm_ring_presentation_morphism_map R A D (@comm_ring_presentation_morphism_comp R A B D g f))
    (@comm_ring_presentation_morphism_map R A D (@comm_ring_presentation_morphism_comp R A C D k h))))
  : τ (@= (@CommRingFreydHomSet R A D)
      (@comp_fapp0 (@CommRingFreydPresentation_cat R) A B D (@comm_ring_freyd_hom_class R B D g) (@comm_ring_freyd_hom_class R A B f))
      (@comp_fapp0 (@CommRingFreydPresentation_cat R) A C D (@comm_ring_freyd_hom_class R C D k) (@comm_ring_freyd_hom_class R A C h)))
≔ @eq_trans _ _ _ _
    (@comm_ring_freyd_comp_usability_path R A B D (@comm_ring_freyd_hom_class R B D g) (@comm_ring_freyd_hom_class R A B f))
    (@eq_trans _ _ _ _
      (@comm_ring_freyd_agreement_path R A D
        (@comm_ring_presentation_morphism_comp R A B D g f)
        (@comm_ring_presentation_morphism_comp R A C D k h) p)
      (@eq_sym _ _ _ (@comm_ring_freyd_comp_usability_path R A C D
        (@comm_ring_freyd_hom_class R C D k) (@comm_ring_freyd_hom_class R A C h))));

symbol freyd_raw_chain_map_generic [R : τ CommRing]
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
  : τ (@ComputationalChainPairMap (@CommRingFreydPresentation_cat R) (@comm_ring_freyd_preadditive R)
      S2 S1 S0 T2 T1 T0 (@freyd_raw_chain_pair_generic R S2 S1 S0 sdNext sd chainS) (@freyd_raw_chain_pair_generic R T2 T1 T0 tdNext td chainT))
≔ @computational_chain_pair_map_of_components (@CommRingFreydPresentation_cat R) (@comm_ring_freyd_preadditive R)
    S2 S1 S0 T2 T1 T0 (@freyd_raw_chain_pair_generic R S2 S1 S0 sdNext sd chainS) (@freyd_raw_chain_pair_generic R T2 T1 T0 tdNext td chainT)
    (@comm_ring_freyd_hom_class R S2 T2 f2) (@comm_ring_freyd_hom_class R S1 T1 f1) (@comm_ring_freyd_hom_class R S0 T0 f0)
    (@freyd_raw_composite_agreement_path R S2 T2 S1 T1 f2 tdNext sdNext f1
      (@comm_ring_freyd_homology_chain_map_upper R S2 S1 S0 T2 T1 T0 sdNext sd tdNext td f2 f1 f0 m))
    (@eq_sym _ _ _ (@freyd_raw_composite_agreement_path R S1 T1 S0 T0 f1 td sd f0
      (@comm_ring_freyd_homology_chain_map_lower R S2 S1 S0 T2 T1 T0 sdNext sd tdNext td f2 f1 f0 m)));

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
