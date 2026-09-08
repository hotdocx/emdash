/* Reviewer-facing witnessed formal Freyd homology consumers. */

require open emdash.emdash3_2_commutative_algebra_freyd_selected_homology;
require open emdash.emdash3_2_commutative_algebra_freyd_homology;

assert
  (R : τ CommRing)
  (P2 P1 P0 : τ (@CommRingPresentation R))
  (dNext : τ (@CommRingPresentationMorphism R P2 P1))
  (d : τ (@CommRingPresentationMorphism R P1 P0))
  (K : τ (@CommRingFreydKernelChoices R P1 P0 d))
  ⊢ @CommRingFreydChainPair R P2 P1 P0 dNext d
  : Grpd;

assert
  (R : τ CommRing)
  (P2 P1 P0 : τ (@CommRingPresentation R))
  (dNext : τ (@CommRingPresentationMorphism R P2 P1))
  (d : τ (@CommRingPresentationMorphism R P1 P0))
  (K : τ (@CommRingFreydKernelChoices R P1 P0 d))
  (chain : τ (@CommRingFreydChainPair R P2 P1 P0 dNext d))
  ⊢ @comm_ring_freyd_selected_witnessed_homology_at R P2 P1 P0 dNext d K chain
  : τ (@CommRingFreydSelectedHomologyAt R P2 P1 P0 dNext d K chain);

assert
  (R : τ CommRing)
  (P2 P1 P0 : τ (@CommRingPresentation R))
  (dNext : τ (@CommRingPresentationMorphism R P2 P1))
  (d : τ (@CommRingPresentationMorphism R P1 P0))
  (K : τ (@CommRingFreydKernelChoices R P1 P0 d))
  (chain : τ (@CommRingFreydChainPair R P2 P1 P0 dNext d))
  (H : τ (@CommRingFreydSelectedHomologyAt R P2 P1 P0 dNext d K chain))
  ⊢ @comm_ring_freyd_selected_homology_boundary_reconstruction_path R P2 P1 P0 dNext d K chain H
  : τ (@= (@CommRingFreydHomSet R P2 P1)
      (@comm_ring_freyd_comp R P2
        (@comm_ring_freyd_selected_homology_cycle_presentation R P2 P1 P0 dNext d K)
        P1
        (@comm_ring_freyd_selected_kernel_embedding R P1 P0 d K)
        (@comm_ring_freyd_selected_homology_boundary R P2 P1 P0 dNext d K chain H))
      (@comm_ring_freyd_hom_class R P2 P1 dNext));

assert
  (R : τ CommRing)
  (P2 P1 P0 : τ (@CommRingPresentation R))
  (dNext : τ (@CommRingPresentationMorphism R P2 P1))
  (d : τ (@CommRingPresentationMorphism R P1 P0))
  (K : τ (@CommRingFreydKernelChoices R P1 P0 d))
  (chain : τ (@CommRingFreydChainPair R P2 P1 P0 dNext d))
  (H : τ (@CommRingFreydSelectedHomologyAt R P2 P1 P0 dNext d K chain))
  ⊢ @comm_ring_freyd_selected_homology_projection_annihilation_path R P2 P1 P0 dNext d K chain H
  : τ (@= (@CommRingFreydHomSet R P2
      (@comm_ring_freyd_selected_homology_presentation R P2 P1 P0 dNext d K chain H))
      (@comm_ring_freyd_comp R P2
        (@comm_ring_freyd_selected_homology_cycle_presentation R P2 P1 P0 dNext d K)
        (@comm_ring_freyd_selected_homology_presentation R P2 P1 P0 dNext d K chain H)
        (@comm_ring_freyd_selected_homology_projection R P2 P1 P0 dNext d K chain H)
        (@comm_ring_freyd_selected_homology_boundary R P2 P1 P0 dNext d K chain H))
      (@comm_ring_freyd_zero_class R P2
        (@comm_ring_freyd_selected_homology_presentation R P2 P1 P0 dNext d K chain H)));

assert
  (R : τ CommRing)
  (P2 P1 P0 : τ (@CommRingPresentation R))
  (dNext : τ (@CommRingPresentationMorphism R P2 P1))
  (d : τ (@CommRingPresentationMorphism R P1 P0))
  (K : τ (@CommRingFreydKernelChoices R P1 P0 d))
  (chain : τ (@CommRingFreydChainPair R P2 P1 P0 dNext d))
  (H : τ (@CommRingFreydSelectedHomologyAt R P2 P1 P0 dNext d K chain))
  (exact : τ (@CommRingFreydSelectedExactnessAt R P2 P1 P0 dNext d K chain H))
  ⊢ @comm_ring_freyd_selected_exactness_projection_zero_path R P2 P1 P0 dNext d K chain H exact
  : τ (@= (@CommRingFreydHomSet R
      (@comm_ring_freyd_selected_homology_cycle_presentation R P2 P1 P0 dNext d K)
      (@comm_ring_freyd_selected_homology_presentation R P2 P1 P0 dNext d K chain H))
      (@comm_ring_freyd_selected_homology_projection R P2 P1 P0 dNext d K chain H)
      (@comm_ring_freyd_zero_class R
        (@comm_ring_freyd_selected_homology_cycle_presentation R P2 P1 P0 dNext d K)
        (@comm_ring_freyd_selected_homology_presentation R P2 P1 P0 dNext d K chain H)));

// The supplied raw boundary is retained literally, not reselected.
assert
  (R : τ CommRing)
  (P2 P1 P0 : τ (@CommRingPresentation R))
  (dNext : τ (@CommRingPresentationMorphism R P2 P1))
  (d : τ (@CommRingPresentationMorphism R P1 P0))
  (K : τ (@CommRingFreydKernelChoices R P1 P0 d))
  (chain : τ (@CommRingFreydChainPair R P2 P1 P0 dNext d))
  (boundary : τ (@CommRingPresentationMorphism R P2 (@comm_ring_freyd_selected_kernel_presentation R P1 P0 d K)))
  (reconstruction : τ (@CommRingPresentationMorphismAgreement R P2 P1
    (@comm_ring_presentation_morphism_map R P2 P1
      (@comm_ring_presentation_morphism_comp R P2 (@comm_ring_freyd_selected_kernel_presentation R P1 P0 d K) P1
        (@comm_ring_freyd_selected_kernel_embedding_raw R P1 P0 d K) boundary))
    (@comm_ring_presentation_morphism_map R P2 P1 dNext)))
  ⊢ @comm_ring_freyd_selected_homology_boundary_raw R P2 P1 P0 dNext d K chain
      (@comm_ring_freyd_selected_homology_from_boundary R P2 P1 P0 dNext d K chain boundary reconstruction) ≡ boundary;

// Exactness concerns exactly that retained raw boundary.
assert
  (R : τ CommRing)
  (P2 P1 P0 : τ (@CommRingPresentation R))
  (dNext : τ (@CommRingPresentationMorphism R P2 P1))
  (d : τ (@CommRingPresentationMorphism R P1 P0))
  (K : τ (@CommRingFreydKernelChoices R P1 P0 d))
  (chain : τ (@CommRingFreydChainPair R P2 P1 P0 dNext d))
  (boundary : τ (@CommRingPresentationMorphism R P2 (@comm_ring_freyd_selected_kernel_presentation R P1 P0 d K)))
  (reconstruction : τ (@CommRingPresentationMorphismAgreement R P2 P1
    (@comm_ring_presentation_morphism_map R P2 P1
      (@comm_ring_presentation_morphism_comp R P2 (@comm_ring_freyd_selected_kernel_presentation R P1 P0 d K) P1
        (@comm_ring_freyd_selected_kernel_embedding_raw R P1 P0 d K) boundary))
    (@comm_ring_presentation_morphism_map R P2 P1 dNext)))
  ⊢ @CommRingFreydSelectedExactnessAt R P2 P1 P0 dNext d K chain
      (@comm_ring_freyd_selected_homology_from_boundary R P2 P1 P0 dNext d K chain boundary reconstruction)
    ≡ @CommRingFreydEpimorphismWitness R P2 (@comm_ring_freyd_selected_kernel_presentation R P1 P0 d K) boundary;

// A separately selected kernel is not a silent replacement for K.
assertnot
  (R : τ CommRing)
  (P2 P1 P0 : τ (@CommRingPresentation R))
  (dNext : τ (@CommRingPresentationMorphism R P2 P1))
  (d : τ (@CommRingPresentationMorphism R P1 P0))
  (K : τ (@CommRingFreydKernelChoices R P1 P0 d))
  (chain : τ (@CommRingFreydChainPair R P2 P1 P0 dNext d))
  (otherK : τ (@CommRingFreydKernelChoices R P1 P0 d))
  (H : τ (@CommRingFreydSelectedHomologyAt R P2 P1 P0 dNext d K chain))
  ⊢ H : τ (@CommRingFreydSelectedHomologyAt R P2 P1 P0 dNext d otherK chain);

// The old whole constructor is exactly the shared constructor at its W choices.
assert
  (R : τ CommRing)
  (W : τ (@HasComputationalWeakKernels (@CommRingFiniteFree_cat R)
    (@comm_ring_finite_free_preadditive R)))
  (P2 P1 P0 : τ (@CommRingPresentation R))
  (dNext : τ (@CommRingPresentationMorphism R P2 P1))
  (d : τ (@CommRingPresentationMorphism R P1 P0))
  (chain : τ (@CommRingFreydChainPair R P2 P1 P0 dNext d))
  ⊢ @comm_ring_freyd_witnessed_homology_at R W P2 P1 P0 dNext d chain
    ≡ @comm_ring_freyd_selected_witnessed_homology_at R P2 P1 P0 dNext d
      (@comm_ring_freyd_kernel_selected_choices R W P1 P0 d) chain;
