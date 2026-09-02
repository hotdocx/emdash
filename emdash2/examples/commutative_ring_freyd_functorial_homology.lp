/* Reviewer-facing witnessed induced Freyd homology-map consumers. */

require open emdash.emdash3_2_commutative_algebra_freyd_functorial_homology;

assert
  (R : τ CommRing)
  (S2 S1 S0 T2 T1 T0 : τ (@CommRingPresentation R))
  (sdNext : τ (@CommRingPresentationMorphism R S2 S1))
  (sd : τ (@CommRingPresentationMorphism R S1 S0))
  (tdNext : τ (@CommRingPresentationMorphism R T2 T1))
  (td : τ (@CommRingPresentationMorphism R T1 T0))
  (f2 : τ (@CommRingPresentationMorphism R S2 T2))
  (f1 : τ (@CommRingPresentationMorphism R S1 T1))
  (f0 : τ (@CommRingPresentationMorphism R S0 T0))
  ⊢ @CommRingFreydHomologyChainMap R
      S2 S1 S0 T2 T1 T0 sdNext sd tdNext td f2 f1 f0
  : Grpd;

assert
  (R : τ CommRing)
  (W : τ (@HasComputationalWeakKernels
    (@CommRingFiniteFree_cat R)
    (@comm_ring_finite_free_preadditive R)))
  (S2 S1 S0 T2 T1 T0 : τ (@CommRingPresentation R))
  (sdNext : τ (@CommRingPresentationMorphism R S2 S1))
  (sd : τ (@CommRingPresentationMorphism R S1 S0))
  (tdNext : τ (@CommRingPresentationMorphism R T2 T1))
  (td : τ (@CommRingPresentationMorphism R T1 T0))
  (f1 : τ (@CommRingPresentationMorphism R S1 T1))
  (cyclesZero : τ (@CommRingFreydHomologyCyclesZeroAgreement R W
    S2 S1 S0 T2 T1 T0 sdNext sd tdNext td f1))
  ⊢ @comm_ring_freyd_homology_cycles_map_raw R W
      S2 S1 S0 T2 T1 T0 sdNext sd tdNext td f1 cyclesZero
  : τ (@CommRingPresentationMorphism R
      (@comm_ring_freyd_homology_cycle_presentation R W S2 S1 S0 sdNext sd)
      (@comm_ring_freyd_homology_cycle_presentation R W T2 T1 T0 tdNext td));

assert
  (R : τ CommRing)
  (W : τ (@HasComputationalWeakKernels
    (@CommRingFiniteFree_cat R)
    (@comm_ring_finite_free_preadditive R)))
  (S2 S1 S0 T2 T1 T0 : τ (@CommRingPresentation R))
  (sdNext : τ (@CommRingPresentationMorphism R S2 S1))
  (sd : τ (@CommRingPresentationMorphism R S1 S0))
  (tdNext : τ (@CommRingPresentationMorphism R T2 T1))
  (td : τ (@CommRingPresentationMorphism R T1 T0))
  (sChain : τ (@CommRingFreydChainPair R S2 S1 S0 sdNext sd))
  (tChain : τ (@CommRingFreydChainPair R T2 T1 T0 tdNext td))
  (SH : τ (@CommRingFreydWitnessedHomologyAt R W
    S2 S1 S0 sdNext sd sChain))
  (TH : τ (@CommRingFreydWitnessedHomologyAt R W
    T2 T1 T0 tdNext td tChain))
  (f2 : τ (@CommRingPresentationMorphism R S2 T2))
  (f1 : τ (@CommRingPresentationMorphism R S1 T1))
  (f0 : τ (@CommRingPresentationMorphism R S0 T0))
  (F : τ (@CommRingFreydHomologyChainMap R
    S2 S1 S0 T2 T1 T0 sdNext sd tdNext td f2 f1 f0))
  (cyclesZero : τ (@CommRingFreydHomologyCyclesZeroAgreement R W
    S2 S1 S0 T2 T1 T0 sdNext sd tdNext td f1))
  (boundaryCompatibility : τ (@CommRingFreydHomologyBoundaryCompatibility
    R W S2 S1 S0 T2 T1 T0 sdNext sd tdNext td sChain tChain
    SH TH f2 f1 cyclesZero))
  (quotientZero : τ (@CommRingFreydHomologyQuotientZeroAgreement R W
    S2 S1 S0 T2 T1 T0 sdNext sd tdNext td
    sChain tChain SH TH f1 cyclesZero))
  ⊢ @comm_ring_freyd_induced_homology_data_intro R W
      S2 S1 S0 T2 T1 T0 sdNext sd tdNext td sChain tChain
      SH TH f2 f1 f0 F cyclesZero boundaryCompatibility quotientZero
  : τ (@CommRingFreydInducedHomologyData R W
      S2 S1 S0 T2 T1 T0 sdNext sd tdNext td sChain tChain
      SH TH f2 f1 f0 F);

assert
  (R : τ CommRing)
  (W : τ (@HasComputationalWeakKernels
    (@CommRingFiniteFree_cat R)
    (@comm_ring_finite_free_preadditive R)))
  (S2 S1 S0 T2 T1 T0 : τ (@CommRingPresentation R))
  (sdNext : τ (@CommRingPresentationMorphism R S2 S1))
  (sd : τ (@CommRingPresentationMorphism R S1 S0))
  (tdNext : τ (@CommRingPresentationMorphism R T2 T1))
  (td : τ (@CommRingPresentationMorphism R T1 T0))
  (sChain : τ (@CommRingFreydChainPair R S2 S1 S0 sdNext sd))
  (tChain : τ (@CommRingFreydChainPair R T2 T1 T0 tdNext td))
  (SH : τ (@CommRingFreydWitnessedHomologyAt R W
    S2 S1 S0 sdNext sd sChain))
  (TH : τ (@CommRingFreydWitnessedHomologyAt R W
    T2 T1 T0 tdNext td tChain))
  (f2 : τ (@CommRingPresentationMorphism R S2 T2))
  (f1 : τ (@CommRingPresentationMorphism R S1 T1))
  (f0 : τ (@CommRingPresentationMorphism R S0 T0))
  (F : τ (@CommRingFreydHomologyChainMap R
    S2 S1 S0 T2 T1 T0 sdNext sd tdNext td f2 f1 f0))
  (data : τ (@CommRingFreydInducedHomologyData R W
    S2 S1 S0 T2 T1 T0 sdNext sd tdNext td sChain tChain
    SH TH f2 f1 f0 F))
  ⊢ @comm_ring_freyd_induced_homology_reconstruction_path R W
      S2 S1 S0 T2 T1 T0 sdNext sd tdNext td sChain tChain
      SH TH f2 f1 f0 F data
  : τ (@= (@CommRingFreydHomSet R
      (@comm_ring_freyd_homology_cycle_presentation R W S2 S1 S0 sdNext sd)
      (@comm_ring_freyd_homology_presentation R W
        T2 T1 T0 tdNext td tChain TH))
      (@comm_ring_freyd_comp R
        (@comm_ring_freyd_homology_cycle_presentation R W S2 S1 S0 sdNext sd)
        (@comm_ring_freyd_homology_presentation R W
          S2 S1 S0 sdNext sd sChain SH)
        (@comm_ring_freyd_homology_presentation R W
          T2 T1 T0 tdNext td tChain TH)
        (@comm_ring_freyd_induced_homology_map R W
          S2 S1 S0 T2 T1 T0 sdNext sd tdNext td sChain tChain
          SH TH f2 f1 f0 F data)
        (@comm_ring_freyd_homology_projection R W
          S2 S1 S0 sdNext sd sChain SH))
      (@comm_ring_freyd_hom_class R
        (@comm_ring_freyd_homology_cycle_presentation R W S2 S1 S0 sdNext sd)
        (@comm_ring_freyd_homology_presentation R W
          T2 T1 T0 tdNext td tChain TH)
        (@comm_ring_freyd_homology_quotient_test_raw R W
          S2 S1 S0 T2 T1 T0 sdNext sd tdNext td sChain tChain SH TH f1
          (@comm_ring_freyd_induced_homology_cycles_zero R W
            S2 S1 S0 T2 T1 T0 sdNext sd tdNext td sChain tChain
            SH TH f2 f1 f0 F data))));
