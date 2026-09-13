/* Shared raw-map observations and their existing path action.
   The two agreement observations are unchanged; no universal selection is used. */
require open emdash.emdash3_2_chain_pair_maps;
require open emdash.emdash3_2_commutative_algebra_freyd_chain_pair_data;
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

// Whole path action of the existing raw-agreement conversion.
symbol freyd_raw_chain_map_path_func [R : τ CommRing]
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
  : τ (Functor (Path_cat (@CommRingFreydHomologyChainMap R S2 S1 S0 T2 T1 T0 sdNext sd tdNext td f2 f1 f0)) (Path_cat (@ComputationalChainPairMap (@CommRingFreydPresentation_cat R) (@comm_ring_freyd_preadditive R) S2 S1 S0 T2 T1 T0 (@freyd_raw_chain_pair_generic R S2 S1 S0 sdNext sd chainS) (@freyd_raw_chain_pair_generic R T2 T1 T0 tdNext td chainT))))
≔ @path_map_func (@CommRingFreydHomologyChainMap R S2 S1 S0 T2 T1 T0 sdNext sd tdNext td f2 f1 f0) (@ComputationalChainPairMap (@CommRingFreydPresentation_cat R) (@comm_ring_freyd_preadditive R) S2 S1 S0 T2 T1 T0 (@freyd_raw_chain_pair_generic R S2 S1 S0 sdNext sd chainS) (@freyd_raw_chain_pair_generic R T2 T1 T0 tdNext td chainT))
    (λ m : τ (@CommRingFreydHomologyChainMap R S2 S1 S0 T2 T1 T0 sdNext sd tdNext td f2 f1 f0), @freyd_raw_chain_map_generic R S2 S1 S0 T2 T1 T0 sdNext sd tdNext td f2 f1 f0 chainS chainT m);
