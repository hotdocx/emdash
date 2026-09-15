/* The native observations retain whole H, raw inputs and Hom action. */
require open emdash.emdash3_2_commutative_algebra_freyd_adjunction_model_observations;
require open emdash.emdash3_2_commutative_algebra_freyd_native_maps;

symbol R : τ CommRing;
symbol M : τ (FreydAdjunctionModel R);
symbol S2 : τ (@CommRingPresentation R);
symbol S1 : τ (@CommRingPresentation R);
symbol S0 : τ (@CommRingPresentation R);
symbol T2 : τ (@CommRingPresentation R);
symbol T1 : τ (@CommRingPresentation R);
symbol T0 : τ (@CommRingPresentation R);
symbol sdNext : τ (@CommRingPresentationMorphism R S2 S1);
symbol sd : τ (@CommRingPresentationMorphism R S1 S0);
symbol tdNext : τ (@CommRingPresentationMorphism R T2 T1);
symbol td : τ (@CommRingPresentationMorphism R T1 T0);
symbol f2 : τ (@CommRingPresentationMorphism R S2 T2);
symbol f1 : τ (@CommRingPresentationMorphism R S1 T1);
symbol f0 : τ (@CommRingPresentationMorphism R S0 T0);
symbol chainS : τ (@CommRingFreydChainPair R S2 S1 S0 sdNext sd);
symbol chainT : τ (@CommRingFreydChainPair R T2 T1 T0 tdNext td);
symbol m0 : τ (@CommRingFreydHomologyChainMap R S2 S1 S0 T2 T1 T0 sdNext sd tdNext td f2 f1 f0);
symbol m1 : τ (@CommRingFreydHomologyChainMap R S2 S1 S0 T2 T1 T0 sdNext sd tdNext td f2 f1 f0);
// Literal native input, with no selected-kernel record.
assert ⊢ @freyd_adjunction_model_object R M S2 S1 S0 sdNext sd chainS ≡
  @fapp0 _ _ (@freyd_adjunction_model_func R M)
    (@freyd_raw_chain_native_cone R S2 S1 S0 sdNext sd chainS);

// The whole map functor remains the original raw-map owner.
assert ⊢ @freyd_adjunction_model_map_func R M S2 S1 S0 T2 T1 T0 sdNext sd tdNext td f2 f1 f0 chainS chainT ≡
  @freyd_raw_chain_adjunction_homology_map_func R (@freyd_adjunction_model_initial R M) (@freyd_adjunction_model_kernels R M) (@freyd_adjunction_model_cokernels R M) S2 S1 S0 T2 T1 T0 sdNext sd tdNext td f2 f1 f0 chainS chainT;

// Its application is the actual H action on the native raw map.
assert ⊢ @freyd_adjunction_model_map R M S2 S1 S0 T2 T1 T0 sdNext sd tdNext td f2 f1 f0 chainS chainT m0 ≡
  @fapp1_fapp0 _ _ (@freyd_adjunction_model_func R M)
    (@freyd_raw_chain_native_cone R S2 S1 S0 sdNext sd chainS)
    (@freyd_raw_chain_native_cone R T2 T1 T0 tdNext td chainT)
    (@freyd_raw_chain_native_map R S2 S1 S0 T2 T1 T0 sdNext sd tdNext td f2 f1 f0 chainS chainT m0);

// Original endpoints and retained Hom action, before any CAS realization.
assert ⊢ @freyd_adjunction_model_map R M S2 S1 S0 T2 T1 T0 sdNext sd tdNext td f2 f1 f0 chainS chainT m0
  : τ (@CommRingFreydHomSet R (@freyd_adjunction_model_object R M S2 S1 S0 sdNext sd chainS) (@freyd_adjunction_model_object R M T2 T1 T0 tdNext td chainT));
assert ⊢ @fapp1_func _ _ (@freyd_adjunction_model_map_func R M S2 S1 S0 T2 T1 T0 sdNext sd tdNext td f2 f1 f0 chainS chainT) m0 m1
  : τ (Functor (Hom_cat (Path_cat (@CommRingFreydHomologyChainMap R S2 S1 S0 T2 T1 T0 sdNext sd tdNext td f2 f1 f0)) m0 m1)
      (Hom_cat (Hom_cat (@CommRingFreydPresentation_cat R) (@freyd_adjunction_model_object R M S2 S1 S0 sdNext sd chainS) (@freyd_adjunction_model_object R M T2 T1 T0 tdNext td chainT)) (@freyd_adjunction_model_map R M S2 S1 S0 T2 T1 T0 sdNext sd tdNext td f2 f1 f0 chainS chainT m0)
        (@freyd_adjunction_model_map R M S2 S1 S0 T2 T1 T0 sdNext sd tdNext td f2 f1 f0 chainS chainT m1)));
