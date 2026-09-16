/*
  Witnessed one-degree homology in the formal Freyd category.

  This compatibility API selects its original W-kernel choices and delegates
  to the shared selected-homology core. Every original signature is retained.
  An explicit agreement d o dNext ~ 0 feeds the existing Freyd kernel lift.
  The whole result stores that boundary, its reconstruction agreement, and the
  existing witnessed cokernel universal property. Exactness is the explicit
  Freyd epimorphism witness for the stored boundary. No quotient-path decoder,
  image equality, rewrite rule, or unification rule is introduced.
*/

require open emdash.emdash3_2_commutative_algebra_presentation_chain_inputs;
require open emdash.emdash3_2_commutative_algebra_freyd_selected_homology;

symbol comm_ring_freyd_homology_cycle_presentation
  [R : τ CommRing]
  (W : τ (@HasComputationalWeakKernels
    (@CommRingFiniteFree_cat R)
    (@comm_ring_finite_free_preadditive R)))
  [P2 P1 P0 : τ (@CommRingPresentation R)]
  [dNext : τ (@CommRingPresentationMorphism R P2 P1)]
  (d : τ (@CommRingPresentationMorphism R P1 P0))
  : τ (@CommRingPresentation R)
≔ @comm_ring_freyd_selected_homology_cycle_presentation R P2 P1 P0 dNext d
    (@comm_ring_freyd_kernel_selected_choices R W P1 P0 d);

symbol comm_ring_freyd_homology_cycle_embedding_raw
  [R : τ CommRing]
  (W : τ (@HasComputationalWeakKernels
    (@CommRingFiniteFree_cat R)
    (@comm_ring_finite_free_preadditive R)))
  [P2 P1 P0 : τ (@CommRingPresentation R)]
  [dNext : τ (@CommRingPresentationMorphism R P2 P1)]
  (d : τ (@CommRingPresentationMorphism R P1 P0))
  : τ (@CommRingPresentationMorphism R
      (@comm_ring_freyd_homology_cycle_presentation R W P2 P1 P0 dNext d)
      P1)
≔ @comm_ring_freyd_selected_homology_cycle_embedding_raw R P2 P1 P0 dNext d
    (@comm_ring_freyd_kernel_selected_choices R W P1 P0 d);

symbol comm_ring_freyd_homology_boundary_selected_raw
  [R : τ CommRing]
  (W : τ (@HasComputationalWeakKernels
    (@CommRingFiniteFree_cat R)
    (@comm_ring_finite_free_preadditive R)))
  [P2 P1 P0 : τ (@CommRingPresentation R)]
  (dNext : τ (@CommRingPresentationMorphism R P2 P1))
  (d : τ (@CommRingPresentationMorphism R P1 P0))
  (chain : τ (@CommRingFreydChainPair R P2 P1 P0 dNext d))
  : τ (@CommRingPresentationMorphism R P2
      (@comm_ring_freyd_homology_cycle_presentation R W P2 P1 P0 dNext d))
≔ @comm_ring_freyd_selected_homology_boundary_selected_raw R P2 P1 P0 dNext d
    (@comm_ring_freyd_kernel_selected_choices R W P1 P0 d) chain;

symbol comm_ring_freyd_homology_boundary_selected_reconstruction_agreement
  [R : τ CommRing]
  (W : τ (@HasComputationalWeakKernels
    (@CommRingFiniteFree_cat R)
    (@comm_ring_finite_free_preadditive R)))
  [P2 P1 P0 : τ (@CommRingPresentation R)]
  (dNext : τ (@CommRingPresentationMorphism R P2 P1))
  (d : τ (@CommRingPresentationMorphism R P1 P0))
  (chain : τ (@CommRingFreydChainPair R P2 P1 P0 dNext d))
  : τ (@CommRingPresentationMorphismAgreement R P2 P1
      (@comm_ring_presentation_morphism_map R P2 P1
        (@comm_ring_presentation_morphism_comp R P2
          (@comm_ring_freyd_homology_cycle_presentation
            R W P2 P1 P0 dNext d) P1
          (@comm_ring_freyd_homology_cycle_embedding_raw
            R W P2 P1 P0 dNext d)
          (@comm_ring_freyd_homology_boundary_selected_raw
            R W P2 P1 P0 dNext d chain)))
      (@comm_ring_presentation_morphism_map R P2 P1 dNext))
≔ @comm_ring_freyd_selected_homology_boundary_selected_reconstruction_agreement R P2 P1 P0 dNext d
    (@comm_ring_freyd_kernel_selected_choices R W P1 P0 d) chain;

// Whole witnessed homology: boundary + reconstruction + its cokernel universal.
symbol CommRingFreydWitnessedHomologyAt
  [R : τ CommRing]
  (W : τ (@HasComputationalWeakKernels
    (@CommRingFiniteFree_cat R)
    (@comm_ring_finite_free_preadditive R)))
  [P2 P1 P0 : τ (@CommRingPresentation R)]
  (dNext : τ (@CommRingPresentationMorphism R P2 P1))
  (d : τ (@CommRingPresentationMorphism R P1 P0))
  (chain : τ (@CommRingFreydChainPair R P2 P1 P0 dNext d))
  : Grpd
≔ @CommRingFreydSelectedHomologyAt R P2 P1 P0 dNext d
    (@comm_ring_freyd_kernel_selected_choices R W P1 P0 d) chain;

symbol comm_ring_freyd_witnessed_homology_at
  [R : τ CommRing]
  (W : τ (@HasComputationalWeakKernels
    (@CommRingFiniteFree_cat R)
    (@comm_ring_finite_free_preadditive R)))
  [P2 P1 P0 : τ (@CommRingPresentation R)]
  (dNext : τ (@CommRingPresentationMorphism R P2 P1))
  (d : τ (@CommRingPresentationMorphism R P1 P0))
  (chain : τ (@CommRingFreydChainPair R P2 P1 P0 dNext d))
  : τ (@CommRingFreydWitnessedHomologyAt R W P2 P1 P0 dNext d chain)
≔ @comm_ring_freyd_selected_witnessed_homology_at R P2 P1 P0 dNext d
    (@comm_ring_freyd_kernel_selected_choices R W P1 P0 d) chain;

symbol comm_ring_freyd_homology_boundary_raw
  [R : τ CommRing]
  [W : τ (@HasComputationalWeakKernels
    (@CommRingFiniteFree_cat R)
    (@comm_ring_finite_free_preadditive R))]
  [P2 P1 P0 : τ (@CommRingPresentation R)]
  [dNext : τ (@CommRingPresentationMorphism R P2 P1)]
  [d : τ (@CommRingPresentationMorphism R P1 P0)]
  [chain : τ (@CommRingFreydChainPair R P2 P1 P0 dNext d)]
  (H : τ (@CommRingFreydWitnessedHomologyAt R W P2 P1 P0 dNext d chain))
  : τ (@CommRingPresentationMorphism R P2
      (@comm_ring_freyd_homology_cycle_presentation R W P2 P1 P0 dNext d))
≔ @comm_ring_freyd_selected_homology_boundary_raw R P2 P1 P0 dNext d
    (@comm_ring_freyd_kernel_selected_choices R W P1 P0 d) chain H;

symbol comm_ring_freyd_homology_boundary_reconstruction_agreement
  [R : τ CommRing]
  [W : τ (@HasComputationalWeakKernels
    (@CommRingFiniteFree_cat R)
    (@comm_ring_finite_free_preadditive R))]
  [P2 P1 P0 : τ (@CommRingPresentation R)]
  [dNext : τ (@CommRingPresentationMorphism R P2 P1)]
  [d : τ (@CommRingPresentationMorphism R P1 P0)]
  [chain : τ (@CommRingFreydChainPair R P2 P1 P0 dNext d)]
  (H : τ (@CommRingFreydWitnessedHomologyAt R W P2 P1 P0 dNext d chain))
  : τ (@CommRingPresentationMorphismAgreement R P2 P1
      (@comm_ring_presentation_morphism_map R P2 P1
        (@comm_ring_presentation_morphism_comp R P2
          (@comm_ring_freyd_homology_cycle_presentation
            R W P2 P1 P0 dNext d) P1
          (@comm_ring_freyd_homology_cycle_embedding_raw
            R W P2 P1 P0 dNext d)
          (@comm_ring_freyd_homology_boundary_raw
            R W P2 P1 P0 dNext d chain H)))
      (@comm_ring_presentation_morphism_map R P2 P1 dNext))
≔ @comm_ring_freyd_selected_homology_boundary_reconstruction_agreement R P2 P1 P0 dNext d
    (@comm_ring_freyd_kernel_selected_choices R W P1 P0 d) chain H;

symbol comm_ring_freyd_homology_cokernel_universal
  [R : τ CommRing]
  [W : τ (@HasComputationalWeakKernels
    (@CommRingFiniteFree_cat R)
    (@comm_ring_finite_free_preadditive R))]
  [P2 P1 P0 : τ (@CommRingPresentation R)]
  [dNext : τ (@CommRingPresentationMorphism R P2 P1)]
  [d : τ (@CommRingPresentationMorphism R P1 P0)]
  [chain : τ (@CommRingFreydChainPair R P2 P1 P0 dNext d)]
  (H : τ (@CommRingFreydWitnessedHomologyAt R W P2 P1 P0 dNext d chain))
  : τ (@CommRingFreydWitnessedCokernelUniversal R P2
      (@comm_ring_freyd_homology_cycle_presentation R W P2 P1 P0 dNext d)
      (@comm_ring_freyd_homology_boundary_raw
        R W P2 P1 P0 dNext d chain H))
≔ @comm_ring_freyd_selected_homology_cokernel_universal R P2 P1 P0 dNext d
    (@comm_ring_freyd_kernel_selected_choices R W P1 P0 d) chain H;

symbol comm_ring_freyd_homology_presentation
  [R : τ CommRing]
  [W : τ (@HasComputationalWeakKernels
    (@CommRingFiniteFree_cat R)
    (@comm_ring_finite_free_preadditive R))]
  [P2 P1 P0 : τ (@CommRingPresentation R)]
  [dNext : τ (@CommRingPresentationMorphism R P2 P1)]
  [d : τ (@CommRingPresentationMorphism R P1 P0)]
  [chain : τ (@CommRingFreydChainPair R P2 P1 P0 dNext d)]
  (H : τ (@CommRingFreydWitnessedHomologyAt R W P2 P1 P0 dNext d chain))
  : τ (@CommRingPresentation R)
≔ @comm_ring_freyd_selected_homology_presentation R P2 P1 P0 dNext d
    (@comm_ring_freyd_kernel_selected_choices R W P1 P0 d) chain H;

symbol comm_ring_freyd_homology_projection_raw
  [R : τ CommRing]
  [W : τ (@HasComputationalWeakKernels
    (@CommRingFiniteFree_cat R)
    (@comm_ring_finite_free_preadditive R))]
  [P2 P1 P0 : τ (@CommRingPresentation R)]
  [dNext : τ (@CommRingPresentationMorphism R P2 P1)]
  [d : τ (@CommRingPresentationMorphism R P1 P0)]
  [chain : τ (@CommRingFreydChainPair R P2 P1 P0 dNext d)]
  (H : τ (@CommRingFreydWitnessedHomologyAt R W P2 P1 P0 dNext d chain))
  : τ (@CommRingPresentationMorphism R
      (@comm_ring_freyd_homology_cycle_presentation R W P2 P1 P0 dNext d)
      (@comm_ring_freyd_homology_presentation R W P2 P1 P0 dNext d chain H))
≔ @comm_ring_freyd_selected_homology_projection_raw R P2 P1 P0 dNext d
    (@comm_ring_freyd_kernel_selected_choices R W P1 P0 d) chain H;

symbol comm_ring_freyd_homology_projection_annihilation_agreement
  [R : τ CommRing]
  [W : τ (@HasComputationalWeakKernels
    (@CommRingFiniteFree_cat R)
    (@comm_ring_finite_free_preadditive R))]
  [P2 P1 P0 : τ (@CommRingPresentation R)]
  [dNext : τ (@CommRingPresentationMorphism R P2 P1)]
  [d : τ (@CommRingPresentationMorphism R P1 P0)]
  [chain : τ (@CommRingFreydChainPair R P2 P1 P0 dNext d)]
  (H : τ (@CommRingFreydWitnessedHomologyAt R W P2 P1 P0 dNext d chain))
  : τ (@CommRingPresentationMorphismAgreement R P2
      (@comm_ring_freyd_homology_presentation R W P2 P1 P0 dNext d chain H)
      (@comm_ring_presentation_morphism_map R P2
        (@comm_ring_freyd_homology_presentation R W P2 P1 P0 dNext d chain H)
        (@comm_ring_presentation_morphism_comp R P2
          (@comm_ring_freyd_homology_cycle_presentation
            R W P2 P1 P0 dNext d)
          (@comm_ring_freyd_homology_presentation
            R W P2 P1 P0 dNext d chain H)
          (@comm_ring_freyd_homology_projection_raw
            R W P2 P1 P0 dNext d chain H)
          (@comm_ring_freyd_homology_boundary_raw
            R W P2 P1 P0 dNext d chain H)))
      (@comm_ring_presentation_morphism_map R P2
        (@comm_ring_freyd_homology_presentation R W P2 P1 P0 dNext d chain H)
        (@comm_ring_presentation_morphism_zero R P2
          (@comm_ring_freyd_homology_presentation
            R W P2 P1 P0 dNext d chain H))))
≔ @comm_ring_freyd_selected_homology_projection_annihilation_agreement R P2 P1 P0 dNext d
    (@comm_ring_freyd_kernel_selected_choices R W P1 P0 d) chain H;

// Exactness at P1 is explicit epicity of the stored boundary map.
symbol CommRingFreydExactnessAt
  [R : τ CommRing]
  [W : τ (@HasComputationalWeakKernels
    (@CommRingFiniteFree_cat R)
    (@comm_ring_finite_free_preadditive R))]
  [P2 P1 P0 : τ (@CommRingPresentation R)]
  [dNext : τ (@CommRingPresentationMorphism R P2 P1)]
  [d : τ (@CommRingPresentationMorphism R P1 P0)]
  [chain : τ (@CommRingFreydChainPair R P2 P1 P0 dNext d)]
  (H : τ (@CommRingFreydWitnessedHomologyAt R W P2 P1 P0 dNext d chain))
  : Grpd
≔ @CommRingFreydSelectedExactnessAt R P2 P1 P0 dNext d
    (@comm_ring_freyd_kernel_selected_choices R W P1 P0 d) chain H;

symbol comm_ring_freyd_exactness_projection_zero_agreement
  [R : τ CommRing]
  [W : τ (@HasComputationalWeakKernels
    (@CommRingFiniteFree_cat R)
    (@comm_ring_finite_free_preadditive R))]
  [P2 P1 P0 : τ (@CommRingPresentation R)]
  [dNext : τ (@CommRingPresentationMorphism R P2 P1)]
  [d : τ (@CommRingPresentationMorphism R P1 P0)]
  [chain : τ (@CommRingFreydChainPair R P2 P1 P0 dNext d)]
  [H : τ (@CommRingFreydWitnessedHomologyAt R W P2 P1 P0 dNext d chain)]
  (exact : τ (@CommRingFreydExactnessAt R W P2 P1 P0 dNext d chain H))
  : τ (@CommRingPresentationMorphismAgreement R
      (@comm_ring_freyd_homology_cycle_presentation R W P2 P1 P0 dNext d)
      (@comm_ring_freyd_homology_presentation R W P2 P1 P0 dNext d chain H)
      (@comm_ring_presentation_morphism_map R
        (@comm_ring_freyd_homology_cycle_presentation R W P2 P1 P0 dNext d)
        (@comm_ring_freyd_homology_presentation R W P2 P1 P0 dNext d chain H)
        (@comm_ring_freyd_homology_projection_raw
          R W P2 P1 P0 dNext d chain H))
      (@comm_ring_presentation_morphism_map R
        (@comm_ring_freyd_homology_cycle_presentation R W P2 P1 P0 dNext d)
        (@comm_ring_freyd_homology_presentation R W P2 P1 P0 dNext d chain H)
        (@comm_ring_presentation_morphism_zero R
          (@comm_ring_freyd_homology_cycle_presentation R W P2 P1 P0 dNext d)
          (@comm_ring_freyd_homology_presentation
            R W P2 P1 P0 dNext d chain H))))
≔ @comm_ring_freyd_selected_exactness_projection_zero_agreement R P2 P1 P0 dNext d
    (@comm_ring_freyd_kernel_selected_choices R W P1 P0 d) chain H exact;

symbol comm_ring_freyd_homology_boundary
  [R : τ CommRing]
  [W : τ (@HasComputationalWeakKernels
    (@CommRingFiniteFree_cat R)
    (@comm_ring_finite_free_preadditive R))]
  [P2 P1 P0 : τ (@CommRingPresentation R)]
  [dNext : τ (@CommRingPresentationMorphism R P2 P1)]
  [d : τ (@CommRingPresentationMorphism R P1 P0)]
  [chain : τ (@CommRingFreydChainPair R P2 P1 P0 dNext d)]
  (H : τ (@CommRingFreydWitnessedHomologyAt R W P2 P1 P0 dNext d chain))
  : τ (@CommRingFreydHomSet R P2
      (@comm_ring_freyd_homology_cycle_presentation R W P2 P1 P0 dNext d))
≔ @comm_ring_freyd_selected_homology_boundary R P2 P1 P0 dNext d
    (@comm_ring_freyd_kernel_selected_choices R W P1 P0 d) chain H;

symbol comm_ring_freyd_homology_projection
  [R : τ CommRing]
  [W : τ (@HasComputationalWeakKernels
    (@CommRingFiniteFree_cat R)
    (@comm_ring_finite_free_preadditive R))]
  [P2 P1 P0 : τ (@CommRingPresentation R)]
  [dNext : τ (@CommRingPresentationMorphism R P2 P1)]
  [d : τ (@CommRingPresentationMorphism R P1 P0)]
  [chain : τ (@CommRingFreydChainPair R P2 P1 P0 dNext d)]
  (H : τ (@CommRingFreydWitnessedHomologyAt R W P2 P1 P0 dNext d chain))
  : τ (@CommRingFreydHomSet R
      (@comm_ring_freyd_homology_cycle_presentation R W P2 P1 P0 dNext d)
      (@comm_ring_freyd_homology_presentation R W P2 P1 P0 dNext d chain H))
≔ @comm_ring_freyd_selected_homology_projection R P2 P1 P0 dNext d
    (@comm_ring_freyd_kernel_selected_choices R W P1 P0 d) chain H;

symbol comm_ring_freyd_homology_boundary_reconstruction_path
  [R : τ CommRing]
  [W : τ (@HasComputationalWeakKernels
    (@CommRingFiniteFree_cat R)
    (@comm_ring_finite_free_preadditive R))]
  [P2 P1 P0 : τ (@CommRingPresentation R)]
  [dNext : τ (@CommRingPresentationMorphism R P2 P1)]
  [d : τ (@CommRingPresentationMorphism R P1 P0)]
  [chain : τ (@CommRingFreydChainPair R P2 P1 P0 dNext d)]
  (H : τ (@CommRingFreydWitnessedHomologyAt R W P2 P1 P0 dNext d chain))
  : τ (@= (@CommRingFreydHomSet R P2 P1)
      (@comm_ring_freyd_comp R P2
        (@comm_ring_freyd_homology_cycle_presentation R W P2 P1 P0 dNext d)
        P1
        (@comm_ring_freyd_kernel_embedding R W P1 P0 d)
        (@comm_ring_freyd_homology_boundary R W P2 P1 P0 dNext d chain H))
      (@comm_ring_freyd_hom_class R P2 P1 dNext))
≔ @comm_ring_freyd_selected_homology_boundary_reconstruction_path R P2 P1 P0 dNext d
    (@comm_ring_freyd_kernel_selected_choices R W P1 P0 d) chain H;

symbol comm_ring_freyd_homology_projection_annihilation_path
  [R : τ CommRing]
  [W : τ (@HasComputationalWeakKernels
    (@CommRingFiniteFree_cat R)
    (@comm_ring_finite_free_preadditive R))]
  [P2 P1 P0 : τ (@CommRingPresentation R)]
  [dNext : τ (@CommRingPresentationMorphism R P2 P1)]
  [d : τ (@CommRingPresentationMorphism R P1 P0)]
  [chain : τ (@CommRingFreydChainPair R P2 P1 P0 dNext d)]
  (H : τ (@CommRingFreydWitnessedHomologyAt R W P2 P1 P0 dNext d chain))
  : τ (@= (@CommRingFreydHomSet R P2
      (@comm_ring_freyd_homology_presentation R W P2 P1 P0 dNext d chain H))
      (@comm_ring_freyd_comp R P2
        (@comm_ring_freyd_homology_cycle_presentation R W P2 P1 P0 dNext d)
        (@comm_ring_freyd_homology_presentation R W P2 P1 P0 dNext d chain H)
        (@comm_ring_freyd_homology_projection R W P2 P1 P0 dNext d chain H)
        (@comm_ring_freyd_homology_boundary R W P2 P1 P0 dNext d chain H))
      (@comm_ring_freyd_zero_class R P2
        (@comm_ring_freyd_homology_presentation R W P2 P1 P0 dNext d chain H)))
≔ @comm_ring_freyd_selected_homology_projection_annihilation_path R P2 P1 P0 dNext d
    (@comm_ring_freyd_kernel_selected_choices R W P1 P0 d) chain H;

symbol comm_ring_freyd_exactness_projection_zero_path
  [R : τ CommRing]
  [W : τ (@HasComputationalWeakKernels
    (@CommRingFiniteFree_cat R)
    (@comm_ring_finite_free_preadditive R))]
  [P2 P1 P0 : τ (@CommRingPresentation R)]
  [dNext : τ (@CommRingPresentationMorphism R P2 P1)]
  [d : τ (@CommRingPresentationMorphism R P1 P0)]
  [chain : τ (@CommRingFreydChainPair R P2 P1 P0 dNext d)]
  [H : τ (@CommRingFreydWitnessedHomologyAt R W P2 P1 P0 dNext d chain)]
  (exact : τ (@CommRingFreydExactnessAt R W P2 P1 P0 dNext d chain H))
  : τ (@= (@CommRingFreydHomSet R
      (@comm_ring_freyd_homology_cycle_presentation R W P2 P1 P0 dNext d)
      (@comm_ring_freyd_homology_presentation R W P2 P1 P0 dNext d chain H))
      (@comm_ring_freyd_homology_projection R W P2 P1 P0 dNext d chain H)
      (@comm_ring_freyd_zero_class R
        (@comm_ring_freyd_homology_cycle_presentation R W P2 P1 P0 dNext d)
        (@comm_ring_freyd_homology_presentation R W P2 P1 P0 dNext d chain H)))
≔ @comm_ring_freyd_selected_exactness_projection_zero_path R P2 P1 P0 dNext d
    (@comm_ring_freyd_kernel_selected_choices R W P1 P0 d) chain H exact;
