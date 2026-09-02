/* Reviewer-facing recursive formal Freyd-complex consumers. */

require open emdash.emdash3_2_commutative_algebra_freyd_bounded_complexes;

assert
  (R : τ CommRing)
  (P2 P1 P0 : τ (@CommRingPresentation R))
  (d2 : τ (@CommRingPresentationMorphism R P2 P1))
  (d1 : τ (@CommRingPresentationMorphism R P1 P0))
  (law : τ (@CommRingFreydChainPair R P2 P1 P0 d2 d1))
  ⊢ @comm_ring_freyd_chain_tail_cons R zero P0 P1 d1
      P2 d2 law
      (@comm_ring_freyd_chain_tail_nil R P1 P2 d2)
  : τ (@CommRingFreydChainTail R (succ zero) P0 P1 d1);

assert
  (R : τ CommRing)
  (P2 P1 P0 : τ (@CommRingPresentation R))
  (d2 : τ (@CommRingPresentationMorphism R P2 P1))
  (d1 : τ (@CommRingPresentationMorphism R P1 P0))
  (law : τ (@CommRingFreydChainPair R P2 P1 P0 d2 d1))
  ⊢ @comm_ring_freyd_chain_tail_next R zero P0 P1 d1
      (@comm_ring_freyd_chain_tail_cons R zero P0 P1 d1
        P2 d2 law (@comm_ring_freyd_chain_tail_nil R P1 P2 d2))
  ≡ P2;

assert
  (R : τ CommRing)
  (P2 P1 P0 : τ (@CommRingPresentation R))
  (d2 : τ (@CommRingPresentationMorphism R P2 P1))
  (d1 : τ (@CommRingPresentationMorphism R P1 P0))
  (law : τ (@CommRingFreydChainPair R P2 P1 P0 d2 d1))
  ⊢ @comm_ring_freyd_bounded_complex_succ R (succ zero) P0 P1 d1
      (@comm_ring_freyd_chain_tail_cons R zero P0 P1 d1
        P2 d2 law (@comm_ring_freyd_chain_tail_nil R P1 P2 d2))
  : τ (@CommRingFreydBoundedComplex R (succ (succ zero)));

assert
  (R : τ CommRing)
  (W : τ (@HasComputationalWeakKernels
    (@CommRingFiniteFree_cat R)
    (@comm_ring_finite_free_preadditive R)))
  (P2 P1 P0 : τ (@CommRingPresentation R))
  (d2 : τ (@CommRingPresentationMorphism R P2 P1))
  (d1 : τ (@CommRingPresentationMorphism R P1 P0))
  (law : τ (@CommRingFreydChainPair R P2 P1 P0 d2 d1))
  ⊢ @comm_ring_freyd_chain_tail_first_homology R W zero P0 P1 d1
      (@comm_ring_freyd_chain_tail_cons R zero P0 P1 d1
        P2 d2 law (@comm_ring_freyd_chain_tail_nil R P1 P2 d2))
  : τ (@CommRingFreydWitnessedHomologyAt R W P2 P1 P0 d2 d1 law);
