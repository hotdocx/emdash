/* A complete H-map observation computes to its existing endpoints and arrow. */
require open emdash.emdash3_2_commutative_algebra_freyd_homology_model_maps;

symbol R : τ CommRing;
symbol M : τ (FreydHomologyModel R);
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
symbol m : τ (@CommRingFreydHomologyChainMap R S2 S1 S0 T2 T1 T0 sdNext sd tdNext td f2 f1 f0);

symbol observed : τ (FreydArrowObservation R)
≔ @freyd_homology_model_arrow_observation R M S2 S1 S0 T2 T1 T0 sdNext sd tdNext td f2 f1 f0 chainS chainT m;
assert ⊢ sigma_Fst observed ≡ @freyd_homology_model_object R M S2 S1 S0 sdNext sd chainS;
assert ⊢ sigma_Fst (sigma_Snd observed) ≡ @freyd_homology_model_object R M T2 T1 T0 tdNext td chainT;
assert ⊢ sigma_Snd (sigma_Snd observed) ≡ @freyd_homology_model_map R M S2 S1 S0 T2 T1 T0 sdNext sd tdNext td f2 f1 f0 chainS chainT m;

assert [R : τ CommRing] [A B : τ (@CommRingPresentation R)]
  (f : τ (@CommRingPresentationMorphism R A B)) ⊢
  sigma_Snd (sigma_Snd (@freyd_raw_arrow_observation R A B f))
  ≡ @comm_ring_freyd_hom_class R A B f;
