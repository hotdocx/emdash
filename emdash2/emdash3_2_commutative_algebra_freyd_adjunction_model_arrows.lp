/* A complete arrow observation of the existing whole native H action.
   LaxArrow retains both native endpoints and the actual H map together. */
require open emdash.emdash3_2_commutative_algebra_freyd_adjunction_model_observations;
require open emdash.emdash3_2_commutative_algebra_freyd_arrow_observations;

// This is the original lax-edge constructor applied to the existing H map.
symbol freyd_adjunction_model_arrow_observation [R : τ CommRing] (M : τ (FreydAdjunctionModel R))
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
≔ @lax_edge (@CommRingFreydPresentation_cat R)
    (@freyd_adjunction_model_object R M S2 S1 S0 sdNext sd chainS)
    (@freyd_adjunction_model_object R M T2 T1 T0 tdNext td chainT)
    (@freyd_adjunction_model_map R M S2 S1 S0 T2 T1 T0 sdNext sd tdNext td f2 f1 f0 chainS chainT m);
