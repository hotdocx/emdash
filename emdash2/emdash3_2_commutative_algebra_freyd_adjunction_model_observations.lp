/* Readable native model observations. Whole H and its existing raw-map
   functor retain action; no ordinary records or additional laws are inputs. */
require open emdash.emdash3_2_commutative_algebra_freyd_adjunction_models;
require open emdash.emdash3_2_commutative_algebra_freyd_adjunction_homology_maps;

// H_M(e,d,chain) is application of the original whole H to the native input.
symbol freyd_adjunction_model_object [R : τ CommRing]
  (M : τ (FreydAdjunctionModel R)) [A B D : τ (@CommRingPresentation R)]
  (e : τ (@CommRingPresentationMorphism R A B))
  (d : τ (@CommRingPresentationMorphism R B D))
  (chain : τ (@CommRingFreydChainPair R A B D e d))
  : τ (@CommRingPresentation R)
≔ @fapp0 _ _ (@freyd_adjunction_model_func R M)
    (@freyd_raw_chain_native_cone R A B D e d chain);

// Specialize the existing whole raw-map functor to the supplied model fields.
symbol freyd_adjunction_model_map_func [R : τ CommRing] (M : τ (FreydAdjunctionModel R))
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
      (Hom_cat (@CommRingFreydPresentation_cat R) (@freyd_adjunction_model_object R M S2 S1 S0 sdNext sd chainS) (@freyd_adjunction_model_object R M T2 T1 T0 tdNext td chainT)))
≔ @freyd_raw_chain_adjunction_homology_map_func R (@freyd_adjunction_model_initial R M) (@freyd_adjunction_model_kernels R M) (@freyd_adjunction_model_cokernels R M) S2 S1 S0 T2 T1 T0 sdNext sd tdNext td f2 f1 f0 chainS chainT;

// Application view; generic fapp continues to own the higher action.
symbol freyd_adjunction_model_map [R : τ CommRing] (M : τ (FreydAdjunctionModel R))
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
  : τ (@CommRingFreydHomSet R (@freyd_adjunction_model_object R M S2 S1 S0 sdNext sd chainS) (@freyd_adjunction_model_object R M T2 T1 T0 tdNext td chainT))
≔ @fapp0 _ _ (@freyd_adjunction_model_map_func R M S2 S1 S0 T2 T1 T0 sdNext sd tdNext td f2 f1 f0 chainS chainT) m;
