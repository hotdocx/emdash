/*
  Witnessed induced maps on formal Freyd homology.

  A chain map retains its two presentation-square agreements. The effective
  native/proof-CAS consumer additionally supplies the computed cycles-zero,
  boundary-compatibility, and quotient-zero agreements. The target kernel
  lift and source cokernel colift then construct the actual cycles and homology
  maps with reconstruction. No quotient-path decoder or runtime rule is used.
*/

require open emdash.emdash3_2_commutative_algebra_presentation_chain_inputs;
require open emdash.emdash3_2_commutative_algebra_freyd_homology;

symbol comm_ring_freyd_homology_cycles_test_raw
  [R : τ CommRing]
  [W : τ (@HasComputationalWeakKernels
    (@CommRingFiniteFree_cat R)
    (@comm_ring_finite_free_preadditive R))]
  [S2 S1 S0 T2 T1 T0 : τ (@CommRingPresentation R)]
  [sdNext : τ (@CommRingPresentationMorphism R S2 S1)]
  [sd : τ (@CommRingPresentationMorphism R S1 S0)]
  [tdNext : τ (@CommRingPresentationMorphism R T2 T1)]
  [td : τ (@CommRingPresentationMorphism R T1 T0)]
  (f1 : τ (@CommRingPresentationMorphism R S1 T1))
  : τ (@CommRingPresentationMorphism R
      (@comm_ring_freyd_homology_cycle_presentation R W S2 S1 S0 sdNext sd)
      T1)
≔ @comm_ring_presentation_morphism_comp R
    (@comm_ring_freyd_homology_cycle_presentation R W S2 S1 S0 sdNext sd)
    S1 T1 f1
    (@comm_ring_freyd_homology_cycle_embedding_raw R W S2 S1 S0 sdNext sd);

symbol CommRingFreydHomologyCyclesZeroAgreement
  [R : τ CommRing]
  [W : τ (@HasComputationalWeakKernels
    (@CommRingFiniteFree_cat R)
    (@comm_ring_finite_free_preadditive R))]
  [S2 S1 S0 T2 T1 T0 : τ (@CommRingPresentation R)]
  [sdNext : τ (@CommRingPresentationMorphism R S2 S1)]
  [sd : τ (@CommRingPresentationMorphism R S1 S0)]
  [tdNext : τ (@CommRingPresentationMorphism R T2 T1)]
  (td : τ (@CommRingPresentationMorphism R T1 T0))
  (f1 : τ (@CommRingPresentationMorphism R S1 T1))
  : Grpd
≔ @CommRingPresentationMorphismAgreement R
    (@comm_ring_freyd_homology_cycle_presentation R W S2 S1 S0 sdNext sd) T0
    (@comm_ring_presentation_morphism_map R
      (@comm_ring_freyd_homology_cycle_presentation R W S2 S1 S0 sdNext sd) T0
      (@comm_ring_presentation_morphism_comp R
        (@comm_ring_freyd_homology_cycle_presentation R W S2 S1 S0 sdNext sd)
        T1 T0 td
        (@comm_ring_freyd_homology_cycles_test_raw R W
          S2 S1 S0 T2 T1 T0 sdNext sd tdNext td f1)))
    (@comm_ring_presentation_morphism_map R
      (@comm_ring_freyd_homology_cycle_presentation R W S2 S1 S0 sdNext sd) T0
      (@comm_ring_presentation_morphism_zero R
        (@comm_ring_freyd_homology_cycle_presentation R W S2 S1 S0 sdNext sd)
        T0));

symbol comm_ring_freyd_homology_cycles_map_raw
  [R : τ CommRing]
  (W : τ (@HasComputationalWeakKernels
    (@CommRingFiniteFree_cat R)
    (@comm_ring_finite_free_preadditive R)))
  [S2 S1 S0 T2 T1 T0 : τ (@CommRingPresentation R)]
  [sdNext : τ (@CommRingPresentationMorphism R S2 S1)]
  [sd : τ (@CommRingPresentationMorphism R S1 S0)]
  [tdNext : τ (@CommRingPresentationMorphism R T2 T1)]
  (td : τ (@CommRingPresentationMorphism R T1 T0))
  (f1 : τ (@CommRingPresentationMorphism R S1 T1))
  (cyclesZero : τ (@CommRingFreydHomologyCyclesZeroAgreement R W
    S2 S1 S0 T2 T1 T0 sdNext sd tdNext td f1))
  : τ (@CommRingPresentationMorphism R
      (@comm_ring_freyd_homology_cycle_presentation R W S2 S1 S0 sdNext sd)
      (@comm_ring_freyd_homology_cycle_presentation R W T2 T1 T0 tdNext td))
≔ @comm_ring_freyd_kernel_lift_raw R W T1 T0
    (@comm_ring_freyd_homology_cycle_presentation R W S2 S1 S0 sdNext sd)
    td
    (@comm_ring_freyd_homology_cycles_test_raw R W
      S2 S1 S0 T2 T1 T0 sdNext sd tdNext td f1)
    cyclesZero;

symbol comm_ring_freyd_homology_cycles_reconstruction_agreement
  [R : τ CommRing]
  (W : τ (@HasComputationalWeakKernels
    (@CommRingFiniteFree_cat R)
    (@comm_ring_finite_free_preadditive R)))
  [S2 S1 S0 T2 T1 T0 : τ (@CommRingPresentation R)]
  [sdNext : τ (@CommRingPresentationMorphism R S2 S1)]
  [sd : τ (@CommRingPresentationMorphism R S1 S0)]
  [tdNext : τ (@CommRingPresentationMorphism R T2 T1)]
  (td : τ (@CommRingPresentationMorphism R T1 T0))
  (f1 : τ (@CommRingPresentationMorphism R S1 T1))
  (cyclesZero : τ (@CommRingFreydHomologyCyclesZeroAgreement R W
    S2 S1 S0 T2 T1 T0 sdNext sd tdNext td f1))
  : τ (@CommRingPresentationMorphismAgreement R
      (@comm_ring_freyd_homology_cycle_presentation R W S2 S1 S0 sdNext sd) T1
      (@comm_ring_presentation_morphism_map R
        (@comm_ring_freyd_homology_cycle_presentation R W S2 S1 S0 sdNext sd) T1
        (@comm_ring_presentation_morphism_comp R
          (@comm_ring_freyd_homology_cycle_presentation R W S2 S1 S0 sdNext sd)
          (@comm_ring_freyd_homology_cycle_presentation R W T2 T1 T0 tdNext td)
          T1
          (@comm_ring_freyd_homology_cycle_embedding_raw
            R W T2 T1 T0 tdNext td)
          (@comm_ring_freyd_homology_cycles_map_raw R W
            S2 S1 S0 T2 T1 T0 sdNext sd tdNext td f1 cyclesZero)))
      (@comm_ring_presentation_morphism_map R
        (@comm_ring_freyd_homology_cycle_presentation R W S2 S1 S0 sdNext sd) T1
        (@comm_ring_freyd_homology_cycles_test_raw R W
          S2 S1 S0 T2 T1 T0 sdNext sd tdNext td f1)))
≔ @comm_ring_freyd_kernel_reconstruction_agreement R W T1 T0
    (@comm_ring_freyd_homology_cycle_presentation R W S2 S1 S0 sdNext sd)
    td
    (@comm_ring_freyd_homology_cycles_test_raw R W
      S2 S1 S0 T2 T1 T0 sdNext sd tdNext td f1)
    cyclesZero;

symbol CommRingFreydHomologyBoundaryCompatibility
  [R : τ CommRing]
  [W : τ (@HasComputationalWeakKernels
    (@CommRingFiniteFree_cat R)
    (@comm_ring_finite_free_preadditive R))]
  [S2 S1 S0 T2 T1 T0 : τ (@CommRingPresentation R)]
  [sdNext : τ (@CommRingPresentationMorphism R S2 S1)]
  [sd : τ (@CommRingPresentationMorphism R S1 S0)]
  [tdNext : τ (@CommRingPresentationMorphism R T2 T1)]
  [td : τ (@CommRingPresentationMorphism R T1 T0)]
  [sChain : τ (@CommRingFreydChainPair R S2 S1 S0 sdNext sd)]
  [tChain : τ (@CommRingFreydChainPair R T2 T1 T0 tdNext td)]
  (SH : τ (@CommRingFreydWitnessedHomologyAt R W
    S2 S1 S0 sdNext sd sChain))
  (TH : τ (@CommRingFreydWitnessedHomologyAt R W
    T2 T1 T0 tdNext td tChain))
  (f2 : τ (@CommRingPresentationMorphism R S2 T2))
  (f1 : τ (@CommRingPresentationMorphism R S1 T1))
  (cyclesZero : τ (@CommRingFreydHomologyCyclesZeroAgreement R W
    S2 S1 S0 T2 T1 T0 sdNext sd tdNext td f1))
  : Grpd
≔ @CommRingPresentationMorphismAgreement R S2
    (@comm_ring_freyd_homology_cycle_presentation R W T2 T1 T0 tdNext td)
    (@comm_ring_presentation_morphism_map R S2
      (@comm_ring_freyd_homology_cycle_presentation R W T2 T1 T0 tdNext td)
      (@comm_ring_presentation_morphism_comp R S2
        (@comm_ring_freyd_homology_cycle_presentation R W S2 S1 S0 sdNext sd)
        (@comm_ring_freyd_homology_cycle_presentation R W T2 T1 T0 tdNext td)
        (@comm_ring_freyd_homology_cycles_map_raw R W
          S2 S1 S0 T2 T1 T0 sdNext sd tdNext td f1 cyclesZero)
        (@comm_ring_freyd_homology_boundary_raw R W
          S2 S1 S0 sdNext sd sChain SH)))
    (@comm_ring_presentation_morphism_map R S2
      (@comm_ring_freyd_homology_cycle_presentation R W T2 T1 T0 tdNext td)
      (@comm_ring_presentation_morphism_comp R S2 T2
        (@comm_ring_freyd_homology_cycle_presentation R W T2 T1 T0 tdNext td)
        (@comm_ring_freyd_homology_boundary_raw R W
          T2 T1 T0 tdNext td tChain TH)
        f2));

symbol comm_ring_freyd_homology_quotient_test_raw
  [R : τ CommRing]
  [W : τ (@HasComputationalWeakKernels
    (@CommRingFiniteFree_cat R)
    (@comm_ring_finite_free_preadditive R))]
  [S2 S1 S0 T2 T1 T0 : τ (@CommRingPresentation R)]
  [sdNext : τ (@CommRingPresentationMorphism R S2 S1)]
  [sd : τ (@CommRingPresentationMorphism R S1 S0)]
  [tdNext : τ (@CommRingPresentationMorphism R T2 T1)]
  [td : τ (@CommRingPresentationMorphism R T1 T0)]
  [sChain : τ (@CommRingFreydChainPair R S2 S1 S0 sdNext sd)]
  [tChain : τ (@CommRingFreydChainPair R T2 T1 T0 tdNext td)]
  [SH : τ (@CommRingFreydWitnessedHomologyAt R W
    S2 S1 S0 sdNext sd sChain)]
  (TH : τ (@CommRingFreydWitnessedHomologyAt R W
    T2 T1 T0 tdNext td tChain))
  (f1 : τ (@CommRingPresentationMorphism R S1 T1))
  (cyclesZero : τ (@CommRingFreydHomologyCyclesZeroAgreement R W
    S2 S1 S0 T2 T1 T0 sdNext sd tdNext td f1))
  : τ (@CommRingPresentationMorphism R
      (@comm_ring_freyd_homology_cycle_presentation R W S2 S1 S0 sdNext sd)
      (@comm_ring_freyd_homology_presentation R W
        T2 T1 T0 tdNext td tChain TH))
≔ @comm_ring_presentation_morphism_comp R
    (@comm_ring_freyd_homology_cycle_presentation R W S2 S1 S0 sdNext sd)
    (@comm_ring_freyd_homology_cycle_presentation R W T2 T1 T0 tdNext td)
    (@comm_ring_freyd_homology_presentation R W
      T2 T1 T0 tdNext td tChain TH)
    (@comm_ring_freyd_homology_projection_raw R W
      T2 T1 T0 tdNext td tChain TH)
    (@comm_ring_freyd_homology_cycles_map_raw R W
      S2 S1 S0 T2 T1 T0 sdNext sd tdNext td f1 cyclesZero);

symbol CommRingFreydHomologyQuotientZeroAgreement
  [R : τ CommRing]
  [W : τ (@HasComputationalWeakKernels
    (@CommRingFiniteFree_cat R)
    (@comm_ring_finite_free_preadditive R))]
  [S2 S1 S0 T2 T1 T0 : τ (@CommRingPresentation R)]
  [sdNext : τ (@CommRingPresentationMorphism R S2 S1)]
  [sd : τ (@CommRingPresentationMorphism R S1 S0)]
  [tdNext : τ (@CommRingPresentationMorphism R T2 T1)]
  [td : τ (@CommRingPresentationMorphism R T1 T0)]
  [sChain : τ (@CommRingFreydChainPair R S2 S1 S0 sdNext sd)]
  [tChain : τ (@CommRingFreydChainPair R T2 T1 T0 tdNext td)]
  (SH : τ (@CommRingFreydWitnessedHomologyAt R W
    S2 S1 S0 sdNext sd sChain))
  (TH : τ (@CommRingFreydWitnessedHomologyAt R W
    T2 T1 T0 tdNext td tChain))
  (f1 : τ (@CommRingPresentationMorphism R S1 T1))
  (cyclesZero : τ (@CommRingFreydHomologyCyclesZeroAgreement R W
    S2 S1 S0 T2 T1 T0 sdNext sd tdNext td f1))
  : Grpd
≔ @CommRingPresentationMorphismAgreement R S2
    (@comm_ring_freyd_homology_presentation R W
      T2 T1 T0 tdNext td tChain TH)
    (@comm_ring_presentation_morphism_map R S2
      (@comm_ring_freyd_homology_presentation R W
        T2 T1 T0 tdNext td tChain TH)
      (@comm_ring_presentation_morphism_comp R S2
        (@comm_ring_freyd_homology_cycle_presentation R W S2 S1 S0 sdNext sd)
        (@comm_ring_freyd_homology_presentation R W
          T2 T1 T0 tdNext td tChain TH)
        (@comm_ring_freyd_homology_quotient_test_raw R W
          S2 S1 S0 T2 T1 T0 sdNext sd tdNext td
          sChain tChain SH TH f1 cyclesZero)
        (@comm_ring_freyd_homology_boundary_raw R W
          S2 S1 S0 sdNext sd sChain SH)))
    (@comm_ring_presentation_morphism_map R S2
      (@comm_ring_freyd_homology_presentation R W
        T2 T1 T0 tdNext td tChain TH)
      (@comm_ring_presentation_morphism_zero R S2
        (@comm_ring_freyd_homology_presentation R W
          T2 T1 T0 tdNext td tChain TH)));

symbol comm_ring_freyd_induced_homology_map_raw
  [R : τ CommRing]
  [W : τ (@HasComputationalWeakKernels
    (@CommRingFiniteFree_cat R)
    (@comm_ring_finite_free_preadditive R))]
  [S2 S1 S0 T2 T1 T0 : τ (@CommRingPresentation R)]
  [sdNext : τ (@CommRingPresentationMorphism R S2 S1)]
  [sd : τ (@CommRingPresentationMorphism R S1 S0)]
  [tdNext : τ (@CommRingPresentationMorphism R T2 T1)]
  [td : τ (@CommRingPresentationMorphism R T1 T0)]
  [sChain : τ (@CommRingFreydChainPair R S2 S1 S0 sdNext sd)]
  [tChain : τ (@CommRingFreydChainPair R T2 T1 T0 tdNext td)]
  (SH : τ (@CommRingFreydWitnessedHomologyAt R W
    S2 S1 S0 sdNext sd sChain))
  (TH : τ (@CommRingFreydWitnessedHomologyAt R W
    T2 T1 T0 tdNext td tChain))
  (f1 : τ (@CommRingPresentationMorphism R S1 T1))
  (cyclesZero : τ (@CommRingFreydHomologyCyclesZeroAgreement R W
    S2 S1 S0 T2 T1 T0 sdNext sd tdNext td f1))
  (quotientZero : τ (@CommRingFreydHomologyQuotientZeroAgreement R W
    S2 S1 S0 T2 T1 T0 sdNext sd tdNext td
    sChain tChain SH TH f1 cyclesZero))
  : τ (@CommRingPresentationMorphism R
      (@comm_ring_freyd_homology_presentation R W
        S2 S1 S0 sdNext sd sChain SH)
      (@comm_ring_freyd_homology_presentation R W
        T2 T1 T0 tdNext td tChain TH))
≔ @comm_ring_freyd_cokernel_colift_raw R S2
    (@comm_ring_freyd_homology_cycle_presentation R W S2 S1 S0 sdNext sd)
    (@comm_ring_freyd_homology_presentation R W
      T2 T1 T0 tdNext td tChain TH)
    (@comm_ring_freyd_homology_boundary_raw R W
      S2 S1 S0 sdNext sd sChain SH)
    (@comm_ring_freyd_homology_quotient_test_raw R W
      S2 S1 S0 T2 T1 T0 sdNext sd tdNext td
      sChain tChain SH TH f1 cyclesZero)
    quotientZero;

symbol comm_ring_freyd_induced_homology_reconstruction_agreement
  [R : τ CommRing]
  [W : τ (@HasComputationalWeakKernels
    (@CommRingFiniteFree_cat R)
    (@comm_ring_finite_free_preadditive R))]
  [S2 S1 S0 T2 T1 T0 : τ (@CommRingPresentation R)]
  [sdNext : τ (@CommRingPresentationMorphism R S2 S1)]
  [sd : τ (@CommRingPresentationMorphism R S1 S0)]
  [tdNext : τ (@CommRingPresentationMorphism R T2 T1)]
  [td : τ (@CommRingPresentationMorphism R T1 T0)]
  [sChain : τ (@CommRingFreydChainPair R S2 S1 S0 sdNext sd)]
  [tChain : τ (@CommRingFreydChainPair R T2 T1 T0 tdNext td)]
  (SH : τ (@CommRingFreydWitnessedHomologyAt R W
    S2 S1 S0 sdNext sd sChain))
  (TH : τ (@CommRingFreydWitnessedHomologyAt R W
    T2 T1 T0 tdNext td tChain))
  (f1 : τ (@CommRingPresentationMorphism R S1 T1))
  (cyclesZero : τ (@CommRingFreydHomologyCyclesZeroAgreement R W
    S2 S1 S0 T2 T1 T0 sdNext sd tdNext td f1))
  (quotientZero : τ (@CommRingFreydHomologyQuotientZeroAgreement R W
    S2 S1 S0 T2 T1 T0 sdNext sd tdNext td
    sChain tChain SH TH f1 cyclesZero))
  : τ (@CommRingPresentationMorphismAgreement R
      (@comm_ring_freyd_homology_cycle_presentation R W S2 S1 S0 sdNext sd)
      (@comm_ring_freyd_homology_presentation R W
        T2 T1 T0 tdNext td tChain TH)
      (@comm_ring_presentation_morphism_map R
        (@comm_ring_freyd_homology_cycle_presentation R W S2 S1 S0 sdNext sd)
        (@comm_ring_freyd_homology_presentation R W
          T2 T1 T0 tdNext td tChain TH)
        (@comm_ring_presentation_morphism_comp R
          (@comm_ring_freyd_homology_cycle_presentation R W S2 S1 S0 sdNext sd)
          (@comm_ring_freyd_homology_presentation R W
            S2 S1 S0 sdNext sd sChain SH)
          (@comm_ring_freyd_homology_presentation R W
            T2 T1 T0 tdNext td tChain TH)
          (@comm_ring_freyd_induced_homology_map_raw R W
            S2 S1 S0 T2 T1 T0 sdNext sd tdNext td
            sChain tChain SH TH f1 cyclesZero quotientZero)
          (@comm_ring_freyd_homology_projection_raw R W
            S2 S1 S0 sdNext sd sChain SH)))
      (@comm_ring_presentation_morphism_map R
        (@comm_ring_freyd_homology_cycle_presentation R W S2 S1 S0 sdNext sd)
        (@comm_ring_freyd_homology_presentation R W
          T2 T1 T0 tdNext td tChain TH)
        (@comm_ring_freyd_homology_quotient_test_raw R W
          S2 S1 S0 T2 T1 T0 sdNext sd tdNext td
          sChain tChain SH TH f1 cyclesZero)))
≔ @comm_ring_freyd_cokernel_reconstruction_agreement R S2
    (@comm_ring_freyd_homology_cycle_presentation R W S2 S1 S0 sdNext sd)
    (@comm_ring_freyd_homology_presentation R W
      T2 T1 T0 tdNext td tChain TH)
    (@comm_ring_freyd_homology_boundary_raw R W
      S2 S1 S0 sdNext sd sChain SH)
    (@comm_ring_freyd_homology_quotient_test_raw R W
      S2 S1 S0 T2 T1 T0 sdNext sd tdNext td
      sChain tChain SH TH f1 cyclesZero)
    quotientZero;

symbol CommRingFreydInducedHomologyData
  [R : τ CommRing]
  (W : τ (@HasComputationalWeakKernels
    (@CommRingFiniteFree_cat R)
    (@comm_ring_finite_free_preadditive R)))
  [S2 S1 S0 T2 T1 T0 : τ (@CommRingPresentation R)]
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
  (_ : τ (@CommRingFreydHomologyChainMap R
    S2 S1 S0 T2 T1 T0 sdNext sd tdNext td f2 f1 f0))
  : Grpd
≔ `Σ_ cyclesZero : τ (@CommRingFreydHomologyCyclesZeroAgreement R W
      S2 S1 S0 T2 T1 T0 sdNext sd tdNext td f1),
   `Σ_ boundaryCompatibility : τ (@CommRingFreydHomologyBoundaryCompatibility
      R W S2 S1 S0 T2 T1 T0 sdNext sd tdNext td sChain tChain
      SH TH f2 f1 cyclesZero),
      @CommRingFreydHomologyQuotientZeroAgreement R W
        S2 S1 S0 T2 T1 T0 sdNext sd tdNext td
        sChain tChain SH TH f1 cyclesZero;

symbol comm_ring_freyd_induced_homology_data_intro
  [R : τ CommRing]
  [W : τ (@HasComputationalWeakKernels
    (@CommRingFiniteFree_cat R)
    (@comm_ring_finite_free_preadditive R))]
  [S2 S1 S0 T2 T1 T0 : τ (@CommRingPresentation R)]
  [sdNext : τ (@CommRingPresentationMorphism R S2 S1)]
  [sd : τ (@CommRingPresentationMorphism R S1 S0)]
  [tdNext : τ (@CommRingPresentationMorphism R T2 T1)]
  [td : τ (@CommRingPresentationMorphism R T1 T0)]
  [sChain : τ (@CommRingFreydChainPair R S2 S1 S0 sdNext sd)]
  [tChain : τ (@CommRingFreydChainPair R T2 T1 T0 tdNext td)]
  [SH : τ (@CommRingFreydWitnessedHomologyAt R W
    S2 S1 S0 sdNext sd sChain)]
  [TH : τ (@CommRingFreydWitnessedHomologyAt R W
    T2 T1 T0 tdNext td tChain)]
  [f2 : τ (@CommRingPresentationMorphism R S2 T2)]
  [f1 : τ (@CommRingPresentationMorphism R S1 T1)]
  [f0 : τ (@CommRingPresentationMorphism R S0 T0)]
  [F : τ (@CommRingFreydHomologyChainMap R
    S2 S1 S0 T2 T1 T0 sdNext sd tdNext td f2 f1 f0)]
  (cyclesZero : τ (@CommRingFreydHomologyCyclesZeroAgreement R W
    S2 S1 S0 T2 T1 T0 sdNext sd tdNext td f1))
  (boundaryCompatibility : τ (@CommRingFreydHomologyBoundaryCompatibility
    R W S2 S1 S0 T2 T1 T0 sdNext sd tdNext td sChain tChain
    SH TH f2 f1 cyclesZero))
  (quotientZero : τ (@CommRingFreydHomologyQuotientZeroAgreement R W
    S2 S1 S0 T2 T1 T0 sdNext sd tdNext td
    sChain tChain SH TH f1 cyclesZero))
  : τ (@CommRingFreydInducedHomologyData R W
      S2 S1 S0 T2 T1 T0 sdNext sd tdNext td sChain tChain
      SH TH f2 f1 f0 F)
≔ @Struct_sigma
    (@CommRingFreydHomologyCyclesZeroAgreement R W
      S2 S1 S0 T2 T1 T0 sdNext sd tdNext td f1)
    (λ cyclesZero0 : τ (@CommRingFreydHomologyCyclesZeroAgreement R W
        S2 S1 S0 T2 T1 T0 sdNext sd tdNext td f1),
      `Σ_ boundaryCompatibility0 : τ (@CommRingFreydHomologyBoundaryCompatibility
        R W S2 S1 S0 T2 T1 T0 sdNext sd tdNext td sChain tChain
        SH TH f2 f1 cyclesZero0),
        @CommRingFreydHomologyQuotientZeroAgreement R W
          S2 S1 S0 T2 T1 T0 sdNext sd tdNext td
          sChain tChain SH TH f1 cyclesZero0)
    cyclesZero
    (@Struct_sigma
      (@CommRingFreydHomologyBoundaryCompatibility R W
        S2 S1 S0 T2 T1 T0 sdNext sd tdNext td sChain tChain
        SH TH f2 f1 cyclesZero)
      (λ _ : τ _,
        @CommRingFreydHomologyQuotientZeroAgreement R W
          S2 S1 S0 T2 T1 T0 sdNext sd tdNext td
          sChain tChain SH TH f1 cyclesZero)
      boundaryCompatibility quotientZero);

symbol comm_ring_freyd_induced_homology_cycles_zero
  [R : τ CommRing]
  [W : τ (@HasComputationalWeakKernels
    (@CommRingFiniteFree_cat R)
    (@comm_ring_finite_free_preadditive R))]
  [S2 S1 S0 T2 T1 T0 : τ (@CommRingPresentation R)]
  [sdNext : τ (@CommRingPresentationMorphism R S2 S1)]
  [sd : τ (@CommRingPresentationMorphism R S1 S0)]
  [tdNext : τ (@CommRingPresentationMorphism R T2 T1)]
  [td : τ (@CommRingPresentationMorphism R T1 T0)]
  [sChain : τ (@CommRingFreydChainPair R S2 S1 S0 sdNext sd)]
  [tChain : τ (@CommRingFreydChainPair R T2 T1 T0 tdNext td)]
  [SH : τ (@CommRingFreydWitnessedHomologyAt R W
    S2 S1 S0 sdNext sd sChain)]
  [TH : τ (@CommRingFreydWitnessedHomologyAt R W
    T2 T1 T0 tdNext td tChain)]
  [f2 : τ (@CommRingPresentationMorphism R S2 T2)]
  [f1 : τ (@CommRingPresentationMorphism R S1 T1)]
  [f0 : τ (@CommRingPresentationMorphism R S0 T0)]
  [F : τ (@CommRingFreydHomologyChainMap R
    S2 S1 S0 T2 T1 T0 sdNext sd tdNext td f2 f1 f0)]
  (data : τ (@CommRingFreydInducedHomologyData R W
    S2 S1 S0 T2 T1 T0 sdNext sd tdNext td sChain tChain
    SH TH f2 f1 f0 F))
  : τ (@CommRingFreydHomologyCyclesZeroAgreement R W
      S2 S1 S0 T2 T1 T0 sdNext sd tdNext td f1)
≔ sigma_Fst data;

symbol comm_ring_freyd_induced_homology_boundary_compatibility
  [R : τ CommRing]
  [W : τ (@HasComputationalWeakKernels
    (@CommRingFiniteFree_cat R)
    (@comm_ring_finite_free_preadditive R))]
  [S2 S1 S0 T2 T1 T0 : τ (@CommRingPresentation R)]
  [sdNext : τ (@CommRingPresentationMorphism R S2 S1)]
  [sd : τ (@CommRingPresentationMorphism R S1 S0)]
  [tdNext : τ (@CommRingPresentationMorphism R T2 T1)]
  [td : τ (@CommRingPresentationMorphism R T1 T0)]
  [sChain : τ (@CommRingFreydChainPair R S2 S1 S0 sdNext sd)]
  [tChain : τ (@CommRingFreydChainPair R T2 T1 T0 tdNext td)]
  [SH : τ (@CommRingFreydWitnessedHomologyAt R W
    S2 S1 S0 sdNext sd sChain)]
  [TH : τ (@CommRingFreydWitnessedHomologyAt R W
    T2 T1 T0 tdNext td tChain)]
  [f2 : τ (@CommRingPresentationMorphism R S2 T2)]
  [f1 : τ (@CommRingPresentationMorphism R S1 T1)]
  [f0 : τ (@CommRingPresentationMorphism R S0 T0)]
  [F : τ (@CommRingFreydHomologyChainMap R
    S2 S1 S0 T2 T1 T0 sdNext sd tdNext td f2 f1 f0)]
  (data : τ (@CommRingFreydInducedHomologyData R W
    S2 S1 S0 T2 T1 T0 sdNext sd tdNext td sChain tChain
    SH TH f2 f1 f0 F))
  : τ (@CommRingFreydHomologyBoundaryCompatibility R W
      S2 S1 S0 T2 T1 T0 sdNext sd tdNext td sChain tChain SH TH
      f2 f1
      (@comm_ring_freyd_induced_homology_cycles_zero R W
        S2 S1 S0 T2 T1 T0 sdNext sd tdNext td sChain tChain
        SH TH f2 f1 f0 F data))
≔ sigma_Fst (sigma_Snd data);

symbol comm_ring_freyd_induced_homology_quotient_zero
  [R : τ CommRing]
  [W : τ (@HasComputationalWeakKernels
    (@CommRingFiniteFree_cat R)
    (@comm_ring_finite_free_preadditive R))]
  [S2 S1 S0 T2 T1 T0 : τ (@CommRingPresentation R)]
  [sdNext : τ (@CommRingPresentationMorphism R S2 S1)]
  [sd : τ (@CommRingPresentationMorphism R S1 S0)]
  [tdNext : τ (@CommRingPresentationMorphism R T2 T1)]
  [td : τ (@CommRingPresentationMorphism R T1 T0)]
  [sChain : τ (@CommRingFreydChainPair R S2 S1 S0 sdNext sd)]
  [tChain : τ (@CommRingFreydChainPair R T2 T1 T0 tdNext td)]
  [SH : τ (@CommRingFreydWitnessedHomologyAt R W
    S2 S1 S0 sdNext sd sChain)]
  [TH : τ (@CommRingFreydWitnessedHomologyAt R W
    T2 T1 T0 tdNext td tChain)]
  [f2 : τ (@CommRingPresentationMorphism R S2 T2)]
  [f1 : τ (@CommRingPresentationMorphism R S1 T1)]
  [f0 : τ (@CommRingPresentationMorphism R S0 T0)]
  [F : τ (@CommRingFreydHomologyChainMap R
    S2 S1 S0 T2 T1 T0 sdNext sd tdNext td f2 f1 f0)]
  (data : τ (@CommRingFreydInducedHomologyData R W
    S2 S1 S0 T2 T1 T0 sdNext sd tdNext td sChain tChain
    SH TH f2 f1 f0 F))
  : τ (@CommRingFreydHomologyQuotientZeroAgreement R W
      S2 S1 S0 T2 T1 T0 sdNext sd tdNext td sChain tChain SH TH f1
      (@comm_ring_freyd_induced_homology_cycles_zero R W
        S2 S1 S0 T2 T1 T0 sdNext sd tdNext td sChain tChain
        SH TH f2 f1 f0 F data))
≔ sigma_Snd (sigma_Snd data);

symbol comm_ring_freyd_induced_homology_map_raw_from_data
  [R : τ CommRing]
  [W : τ (@HasComputationalWeakKernels
    (@CommRingFiniteFree_cat R)
    (@comm_ring_finite_free_preadditive R))]
  [S2 S1 S0 T2 T1 T0 : τ (@CommRingPresentation R)]
  [sdNext : τ (@CommRingPresentationMorphism R S2 S1)]
  [sd : τ (@CommRingPresentationMorphism R S1 S0)]
  [tdNext : τ (@CommRingPresentationMorphism R T2 T1)]
  [td : τ (@CommRingPresentationMorphism R T1 T0)]
  [sChain : τ (@CommRingFreydChainPair R S2 S1 S0 sdNext sd)]
  [tChain : τ (@CommRingFreydChainPair R T2 T1 T0 tdNext td)]
  [SH : τ (@CommRingFreydWitnessedHomologyAt R W
    S2 S1 S0 sdNext sd sChain)]
  [TH : τ (@CommRingFreydWitnessedHomologyAt R W
    T2 T1 T0 tdNext td tChain)]
  [f2 : τ (@CommRingPresentationMorphism R S2 T2)]
  [f1 : τ (@CommRingPresentationMorphism R S1 T1)]
  [f0 : τ (@CommRingPresentationMorphism R S0 T0)]
  [F : τ (@CommRingFreydHomologyChainMap R
    S2 S1 S0 T2 T1 T0 sdNext sd tdNext td f2 f1 f0)]
  (data : τ (@CommRingFreydInducedHomologyData R W
    S2 S1 S0 T2 T1 T0 sdNext sd tdNext td sChain tChain
    SH TH f2 f1 f0 F))
  : τ (@CommRingPresentationMorphism R
      (@comm_ring_freyd_homology_presentation R W
        S2 S1 S0 sdNext sd sChain SH)
      (@comm_ring_freyd_homology_presentation R W
        T2 T1 T0 tdNext td tChain TH))
≔ @comm_ring_freyd_induced_homology_map_raw R W
    S2 S1 S0 T2 T1 T0 sdNext sd tdNext td sChain tChain SH TH f1
    (@comm_ring_freyd_induced_homology_cycles_zero R W
      S2 S1 S0 T2 T1 T0 sdNext sd tdNext td sChain tChain
      SH TH f2 f1 f0 F data)
    (@comm_ring_freyd_induced_homology_quotient_zero R W
      S2 S1 S0 T2 T1 T0 sdNext sd tdNext td sChain tChain
      SH TH f2 f1 f0 F data);

symbol comm_ring_freyd_induced_homology_map
  [R : τ CommRing]
  [W : τ (@HasComputationalWeakKernels
    (@CommRingFiniteFree_cat R)
    (@comm_ring_finite_free_preadditive R))]
  [S2 S1 S0 T2 T1 T0 : τ (@CommRingPresentation R)]
  [sdNext : τ (@CommRingPresentationMorphism R S2 S1)]
  [sd : τ (@CommRingPresentationMorphism R S1 S0)]
  [tdNext : τ (@CommRingPresentationMorphism R T2 T1)]
  [td : τ (@CommRingPresentationMorphism R T1 T0)]
  [sChain : τ (@CommRingFreydChainPair R S2 S1 S0 sdNext sd)]
  [tChain : τ (@CommRingFreydChainPair R T2 T1 T0 tdNext td)]
  [SH : τ (@CommRingFreydWitnessedHomologyAt R W
    S2 S1 S0 sdNext sd sChain)]
  [TH : τ (@CommRingFreydWitnessedHomologyAt R W
    T2 T1 T0 tdNext td tChain)]
  [f2 : τ (@CommRingPresentationMorphism R S2 T2)]
  [f1 : τ (@CommRingPresentationMorphism R S1 T1)]
  [f0 : τ (@CommRingPresentationMorphism R S0 T0)]
  [F : τ (@CommRingFreydHomologyChainMap R
    S2 S1 S0 T2 T1 T0 sdNext sd tdNext td f2 f1 f0)]
  (data : τ (@CommRingFreydInducedHomologyData R W
    S2 S1 S0 T2 T1 T0 sdNext sd tdNext td sChain tChain
    SH TH f2 f1 f0 F))
  : τ (@CommRingFreydHomSet R
      (@comm_ring_freyd_homology_presentation R W
        S2 S1 S0 sdNext sd sChain SH)
      (@comm_ring_freyd_homology_presentation R W
        T2 T1 T0 tdNext td tChain TH))
≔ @comm_ring_freyd_hom_class R
    (@comm_ring_freyd_homology_presentation R W
      S2 S1 S0 sdNext sd sChain SH)
    (@comm_ring_freyd_homology_presentation R W
      T2 T1 T0 tdNext td tChain TH)
    (@comm_ring_freyd_induced_homology_map_raw_from_data R W
      S2 S1 S0 T2 T1 T0 sdNext sd tdNext td sChain tChain
      SH TH f2 f1 f0 F data);

symbol comm_ring_freyd_induced_homology_reconstruction_from_data
  [R : τ CommRing]
  [W : τ (@HasComputationalWeakKernels
    (@CommRingFiniteFree_cat R)
    (@comm_ring_finite_free_preadditive R))]
  [S2 S1 S0 T2 T1 T0 : τ (@CommRingPresentation R)]
  [sdNext : τ (@CommRingPresentationMorphism R S2 S1)]
  [sd : τ (@CommRingPresentationMorphism R S1 S0)]
  [tdNext : τ (@CommRingPresentationMorphism R T2 T1)]
  [td : τ (@CommRingPresentationMorphism R T1 T0)]
  [sChain : τ (@CommRingFreydChainPair R S2 S1 S0 sdNext sd)]
  [tChain : τ (@CommRingFreydChainPair R T2 T1 T0 tdNext td)]
  [SH : τ (@CommRingFreydWitnessedHomologyAt R W
    S2 S1 S0 sdNext sd sChain)]
  [TH : τ (@CommRingFreydWitnessedHomologyAt R W
    T2 T1 T0 tdNext td tChain)]
  [f2 : τ (@CommRingPresentationMorphism R S2 T2)]
  [f1 : τ (@CommRingPresentationMorphism R S1 T1)]
  [f0 : τ (@CommRingPresentationMorphism R S0 T0)]
  [F : τ (@CommRingFreydHomologyChainMap R
    S2 S1 S0 T2 T1 T0 sdNext sd tdNext td f2 f1 f0)]
  (data : τ (@CommRingFreydInducedHomologyData R W
    S2 S1 S0 T2 T1 T0 sdNext sd tdNext td sChain tChain
    SH TH f2 f1 f0 F))
  : τ (@CommRingPresentationMorphismAgreement R
      (@comm_ring_freyd_homology_cycle_presentation R W S2 S1 S0 sdNext sd)
      (@comm_ring_freyd_homology_presentation R W
        T2 T1 T0 tdNext td tChain TH)
      (@comm_ring_presentation_morphism_map R
        (@comm_ring_freyd_homology_cycle_presentation R W S2 S1 S0 sdNext sd)
        (@comm_ring_freyd_homology_presentation R W
          T2 T1 T0 tdNext td tChain TH)
        (@comm_ring_presentation_morphism_comp R
          (@comm_ring_freyd_homology_cycle_presentation R W S2 S1 S0 sdNext sd)
          (@comm_ring_freyd_homology_presentation R W
            S2 S1 S0 sdNext sd sChain SH)
          (@comm_ring_freyd_homology_presentation R W
            T2 T1 T0 tdNext td tChain TH)
          (@comm_ring_freyd_induced_homology_map_raw_from_data R W
            S2 S1 S0 T2 T1 T0 sdNext sd tdNext td sChain tChain
            SH TH f2 f1 f0 F data)
          (@comm_ring_freyd_homology_projection_raw R W
            S2 S1 S0 sdNext sd sChain SH)))
      (@comm_ring_presentation_morphism_map R
        (@comm_ring_freyd_homology_cycle_presentation R W S2 S1 S0 sdNext sd)
        (@comm_ring_freyd_homology_presentation R W
          T2 T1 T0 tdNext td tChain TH)
        (@comm_ring_freyd_homology_quotient_test_raw R W
          S2 S1 S0 T2 T1 T0 sdNext sd tdNext td sChain tChain SH TH f1
          (@comm_ring_freyd_induced_homology_cycles_zero R W
            S2 S1 S0 T2 T1 T0 sdNext sd tdNext td sChain tChain
            SH TH f2 f1 f0 F data))))
≔ @comm_ring_freyd_induced_homology_reconstruction_agreement R W
    S2 S1 S0 T2 T1 T0 sdNext sd tdNext td sChain tChain SH TH f1
    (@comm_ring_freyd_induced_homology_cycles_zero R W
      S2 S1 S0 T2 T1 T0 sdNext sd tdNext td sChain tChain
      SH TH f2 f1 f0 F data)
    (@comm_ring_freyd_induced_homology_quotient_zero R W
      S2 S1 S0 T2 T1 T0 sdNext sd tdNext td sChain tChain
      SH TH f2 f1 f0 F data);

symbol comm_ring_freyd_induced_homology_reconstruction_path
  [R : τ CommRing]
  [W : τ (@HasComputationalWeakKernels
    (@CommRingFiniteFree_cat R)
    (@comm_ring_finite_free_preadditive R))]
  [S2 S1 S0 T2 T1 T0 : τ (@CommRingPresentation R)]
  [sdNext : τ (@CommRingPresentationMorphism R S2 S1)]
  [sd : τ (@CommRingPresentationMorphism R S1 S0)]
  [tdNext : τ (@CommRingPresentationMorphism R T2 T1)]
  [td : τ (@CommRingPresentationMorphism R T1 T0)]
  [sChain : τ (@CommRingFreydChainPair R S2 S1 S0 sdNext sd)]
  [tChain : τ (@CommRingFreydChainPair R T2 T1 T0 tdNext td)]
  [SH : τ (@CommRingFreydWitnessedHomologyAt R W
    S2 S1 S0 sdNext sd sChain)]
  [TH : τ (@CommRingFreydWitnessedHomologyAt R W
    T2 T1 T0 tdNext td tChain)]
  [f2 : τ (@CommRingPresentationMorphism R S2 T2)]
  [f1 : τ (@CommRingPresentationMorphism R S1 T1)]
  [f0 : τ (@CommRingPresentationMorphism R S0 T0)]
  [F : τ (@CommRingFreydHomologyChainMap R
    S2 S1 S0 T2 T1 T0 sdNext sd tdNext td f2 f1 f0)]
  (data : τ (@CommRingFreydInducedHomologyData R W
    S2 S1 S0 T2 T1 T0 sdNext sd tdNext td sChain tChain
    SH TH f2 f1 f0 F))
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
            SH TH f2 f1 f0 F data))))
≔ @comm_ring_freyd_agreement_path R
    (@comm_ring_freyd_homology_cycle_presentation R W S2 S1 S0 sdNext sd)
    (@comm_ring_freyd_homology_presentation R W
      T2 T1 T0 tdNext td tChain TH)
    (@comm_ring_presentation_morphism_comp R
      (@comm_ring_freyd_homology_cycle_presentation R W S2 S1 S0 sdNext sd)
      (@comm_ring_freyd_homology_presentation R W
        S2 S1 S0 sdNext sd sChain SH)
      (@comm_ring_freyd_homology_presentation R W
        T2 T1 T0 tdNext td tChain TH)
      (@comm_ring_freyd_induced_homology_map_raw_from_data R W
        S2 S1 S0 T2 T1 T0 sdNext sd tdNext td sChain tChain
        SH TH f2 f1 f0 F data)
      (@comm_ring_freyd_homology_projection_raw R W
        S2 S1 S0 sdNext sd sChain SH))
    (@comm_ring_freyd_homology_quotient_test_raw R W
      S2 S1 S0 T2 T1 T0 sdNext sd tdNext td sChain tChain SH TH f1
      (@comm_ring_freyd_induced_homology_cycles_zero R W
        S2 S1 S0 T2 T1 T0 sdNext sd tdNext td sChain tChain
        SH TH f2 f1 f0 F data))
    (@comm_ring_freyd_induced_homology_reconstruction_from_data R W
      S2 S1 S0 T2 T1 T0 sdNext sd tdNext td sChain tChain
      SH TH f2 f1 f0 F data);
