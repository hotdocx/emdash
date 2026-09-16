/* Raw chain-pair and chain-map agreements between fixed presentations.
   Shared by native whole-universality inputs and retained ordinary consumers.
   These classifiers/projections choose no kernel, cokernel or homology.
   Their existing names and declaration bodies are retained from the former
   homology owners; all mathematical dependencies are raw presentation data. */
require open emdash.emdash3_2_commutative_algebra_presentation_operations;
require open emdash.emdash3_2_commutative_algebra_presentation_additive_operations;

symbol CommRingFreydChainPair
  [R : τ CommRing]
  [P2 P1 P0 : τ (@CommRingPresentation R)]
  (dNext : τ (@CommRingPresentationMorphism R P2 P1))
  (d : τ (@CommRingPresentationMorphism R P1 P0))
  : Grpd
≔ @CommRingPresentationMorphismAgreement R P2 P0
    (@comm_ring_presentation_morphism_map R P2 P0
      (@comm_ring_presentation_morphism_comp R P2 P1 P0 d dNext))
    (@comm_ring_presentation_morphism_map R P2 P0
      (@comm_ring_presentation_morphism_zero R P2 P0));

symbol CommRingFreydHomologyChainMap
  [R : τ CommRing]
  [S2 S1 S0 T2 T1 T0 : τ (@CommRingPresentation R)]
  (sdNext : τ (@CommRingPresentationMorphism R S2 S1))
  (sd : τ (@CommRingPresentationMorphism R S1 S0))
  (tdNext : τ (@CommRingPresentationMorphism R T2 T1))
  (td : τ (@CommRingPresentationMorphism R T1 T0))
  (f2 : τ (@CommRingPresentationMorphism R S2 T2))
  (f1 : τ (@CommRingPresentationMorphism R S1 T1))
  (f0 : τ (@CommRingPresentationMorphism R S0 T0))
  : Grpd
≔ @Product_grpd
    (@CommRingPresentationMorphismAgreement R S2 T1
      (@comm_ring_presentation_morphism_map R S2 T1
        (@comm_ring_presentation_morphism_comp R S2 T2 T1 tdNext f2))
      (@comm_ring_presentation_morphism_map R S2 T1
        (@comm_ring_presentation_morphism_comp R S2 S1 T1 f1 sdNext)))
    (@CommRingPresentationMorphismAgreement R S1 T0
      (@comm_ring_presentation_morphism_map R S1 T0
        (@comm_ring_presentation_morphism_comp R S1 T1 T0 td f1))
      (@comm_ring_presentation_morphism_map R S1 T0
        (@comm_ring_presentation_morphism_comp R S1 S0 T0 f0 sd)));

symbol comm_ring_freyd_homology_chain_map_upper
  [R : τ CommRing]
  [S2 S1 S0 T2 T1 T0 : τ (@CommRingPresentation R)]
  [sdNext : τ (@CommRingPresentationMorphism R S2 S1)]
  [sd : τ (@CommRingPresentationMorphism R S1 S0)]
  [tdNext : τ (@CommRingPresentationMorphism R T2 T1)]
  [td : τ (@CommRingPresentationMorphism R T1 T0)]
  [f2 : τ (@CommRingPresentationMorphism R S2 T2)]
  [f1 : τ (@CommRingPresentationMorphism R S1 T1)]
  [f0 : τ (@CommRingPresentationMorphism R S0 T0)]
  (F : τ (@CommRingFreydHomologyChainMap R
    S2 S1 S0 T2 T1 T0 sdNext sd tdNext td f2 f1 f0))
  : τ (@CommRingPresentationMorphismAgreement R S2 T1
      (@comm_ring_presentation_morphism_map R S2 T1
        (@comm_ring_presentation_morphism_comp R S2 T2 T1 tdNext f2))
      (@comm_ring_presentation_morphism_map R S2 T1
        (@comm_ring_presentation_morphism_comp R S2 S1 T1 f1 sdNext)))
≔ sigma_Fst F;

symbol comm_ring_freyd_homology_chain_map_lower
  [R : τ CommRing]
  [S2 S1 S0 T2 T1 T0 : τ (@CommRingPresentation R)]
  [sdNext : τ (@CommRingPresentationMorphism R S2 S1)]
  [sd : τ (@CommRingPresentationMorphism R S1 S0)]
  [tdNext : τ (@CommRingPresentationMorphism R T2 T1)]
  [td : τ (@CommRingPresentationMorphism R T1 T0)]
  [f2 : τ (@CommRingPresentationMorphism R S2 T2)]
  [f1 : τ (@CommRingPresentationMorphism R S1 T1)]
  [f0 : τ (@CommRingPresentationMorphism R S0 T0)]
  (F : τ (@CommRingFreydHomologyChainMap R
    S2 S1 S0 T2 T1 T0 sdNext sd tdNext td f2 f1 f0))
  : τ (@CommRingPresentationMorphismAgreement R S1 T0
      (@comm_ring_presentation_morphism_map R S1 T0
        (@comm_ring_presentation_morphism_comp R S1 T1 T0 td f1))
      (@comm_ring_presentation_morphism_map R S1 T0
        (@comm_ring_presentation_morphism_comp R S1 S0 T0 f0 sd)))
≔ sigma_Snd F;
