/* Whole model H on a retained raw map, plus complete arrow observations. */
require open emdash.emdash3_2_commutative_algebra_freyd_homology_models;

symbol freyd_homology_model_map [R : τ CommRing] (M : τ (FreydHomologyModel R))
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
  : τ (@CommRingFreydHomSet R (@freyd_homology_model_object R M S2 S1 S0 sdNext sd chainS) (@freyd_homology_model_object R M T2 T1 T0 tdNext td chainT))
≔ @fapp1_fapp0 _ _ (@freyd_homology_model_func R M) (@freyd_homology_model_input R M S2 S1 S0 sdNext sd chainS) (@freyd_homology_model_input R M T2 T1 T0 tdNext td chainT)
    (@freyd_raw_chain_zero_cone_map R (@freyd_homology_model_kernels R M) (@freyd_homology_model_kernel_presentation R M)
      S2 S1 S0 T2 T1 T0 sdNext sd tdNext td f2 f1 f0 chainS chainT m);

// This is the EXISTING native arrow-object carrier, not a new diagram record.
symbol FreydArrowObservation (R : τ CommRing) : Grpd
≔ Obj (@LaxArrow_cat (@CommRingFreydPresentation_cat R));

symbol freyd_raw_arrow_observation [R : τ CommRing]
  [A B : τ (@CommRingPresentation R)] (f : τ (@CommRingPresentationMorphism R A B))
  : τ (FreydArrowObservation R)
≔ @lax_edge (@CommRingFreydPresentation_cat R) A B (@comm_ring_freyd_hom_class R A B f);

symbol freyd_homology_model_arrow_observation [R : τ CommRing] (M : τ (FreydHomologyModel R))
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
  : τ (FreydArrowObservation R)
≔ @lax_edge (@CommRingFreydPresentation_cat R) (@freyd_homology_model_object R M S2 S1 S0 sdNext sd chainS) (@freyd_homology_model_object R M T2 T1 T0 tdNext td chainT)
    (@freyd_homology_model_map R M S2 S1 S0 T2 T1 T0 sdNext sd tdNext td f2 f1 f0 chainS chainT m);
