/* Reviewer-facing witnessed formal Freyd homology consumers. */

require open emdash.emdash3_2_commutative_algebra_freyd_homology;

assert
  (R : τ CommRing)
  (P2 P1 P0 : τ (@CommRingPresentation R))
  (dNext : τ (@CommRingPresentationMorphism R P2 P1))
  (d : τ (@CommRingPresentationMorphism R P1 P0))
  ⊢ @CommRingFreydChainPair R P2 P1 P0 dNext d
  : Grpd;

assert
  (R : τ CommRing)
  (W : τ (@HasComputationalWeakKernels
    (@CommRingFiniteFree_cat R)
    (@comm_ring_finite_free_preadditive R)))
  (P2 P1 P0 : τ (@CommRingPresentation R))
  (dNext : τ (@CommRingPresentationMorphism R P2 P1))
  (d : τ (@CommRingPresentationMorphism R P1 P0))
  (chain : τ (@CommRingFreydChainPair R P2 P1 P0 dNext d))
  ⊢ @comm_ring_freyd_witnessed_homology_at
      R W P2 P1 P0 dNext d chain
  : τ (@CommRingFreydWitnessedHomologyAt
      R W P2 P1 P0 dNext d chain);

assert
  (R : τ CommRing)
  (W : τ (@HasComputationalWeakKernels
    (@CommRingFiniteFree_cat R)
    (@comm_ring_finite_free_preadditive R)))
  (P2 P1 P0 : τ (@CommRingPresentation R))
  (dNext : τ (@CommRingPresentationMorphism R P2 P1))
  (d : τ (@CommRingPresentationMorphism R P1 P0))
  (chain : τ (@CommRingFreydChainPair R P2 P1 P0 dNext d))
  (H : τ (@CommRingFreydWitnessedHomologyAt
    R W P2 P1 P0 dNext d chain))
  ⊢ @comm_ring_freyd_homology_boundary_reconstruction_path
      R W P2 P1 P0 dNext d chain H
  : τ (@= (@CommRingFreydHomSet R P2 P1)
      (@comm_ring_freyd_comp R P2
        (@comm_ring_freyd_homology_cycle_presentation R W P2 P1 P0 dNext d)
        P1
        (@comm_ring_freyd_kernel_embedding R W P1 P0 d)
        (@comm_ring_freyd_homology_boundary R W P2 P1 P0 dNext d chain H))
      (@comm_ring_freyd_hom_class R P2 P1 dNext));

assert
  (R : τ CommRing)
  (W : τ (@HasComputationalWeakKernels
    (@CommRingFiniteFree_cat R)
    (@comm_ring_finite_free_preadditive R)))
  (P2 P1 P0 : τ (@CommRingPresentation R))
  (dNext : τ (@CommRingPresentationMorphism R P2 P1))
  (d : τ (@CommRingPresentationMorphism R P1 P0))
  (chain : τ (@CommRingFreydChainPair R P2 P1 P0 dNext d))
  (H : τ (@CommRingFreydWitnessedHomologyAt
    R W P2 P1 P0 dNext d chain))
  ⊢ @comm_ring_freyd_homology_projection_annihilation_path
      R W P2 P1 P0 dNext d chain H
  : τ (@= (@CommRingFreydHomSet R P2
      (@comm_ring_freyd_homology_presentation R W P2 P1 P0 dNext d chain H))
      (@comm_ring_freyd_comp R P2
        (@comm_ring_freyd_homology_cycle_presentation R W P2 P1 P0 dNext d)
        (@comm_ring_freyd_homology_presentation R W P2 P1 P0 dNext d chain H)
        (@comm_ring_freyd_homology_projection R W P2 P1 P0 dNext d chain H)
        (@comm_ring_freyd_homology_boundary R W P2 P1 P0 dNext d chain H))
      (@comm_ring_freyd_zero_class R P2
        (@comm_ring_freyd_homology_presentation R W P2 P1 P0 dNext d chain H)));

assert
  (R : τ CommRing)
  (W : τ (@HasComputationalWeakKernels
    (@CommRingFiniteFree_cat R)
    (@comm_ring_finite_free_preadditive R)))
  (P2 P1 P0 : τ (@CommRingPresentation R))
  (dNext : τ (@CommRingPresentationMorphism R P2 P1))
  (d : τ (@CommRingPresentationMorphism R P1 P0))
  (chain : τ (@CommRingFreydChainPair R P2 P1 P0 dNext d))
  (H : τ (@CommRingFreydWitnessedHomologyAt
    R W P2 P1 P0 dNext d chain))
  (exact : τ (@CommRingFreydExactnessAt
    R W P2 P1 P0 dNext d chain H))
  ⊢ @comm_ring_freyd_exactness_projection_zero_path
      R W P2 P1 P0 dNext d chain H exact
  : τ (@= (@CommRingFreydHomSet R
      (@comm_ring_freyd_homology_cycle_presentation R W P2 P1 P0 dNext d)
      (@comm_ring_freyd_homology_presentation R W P2 P1 P0 dNext d chain H))
      (@comm_ring_freyd_homology_projection R W P2 P1 P0 dNext d chain H)
      (@comm_ring_freyd_zero_class R
        (@comm_ring_freyd_homology_cycle_presentation R W P2 P1 P0 dNext d)
        (@comm_ring_freyd_homology_presentation R W P2 P1 P0 dNext d chain H)));
