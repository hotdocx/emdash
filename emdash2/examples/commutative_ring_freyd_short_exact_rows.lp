/* Whole row evidence and wrong-homology guard. */
require open emdash.emdash3_2_commutative_algebra_freyd_short_exact_rows;

assert
  (R : τ CommRing)
  (W : τ (@HasComputationalWeakKernels
    (@CommRingFiniteFree_cat R) (@comm_ring_finite_free_preadditive R)))
  (A B C : τ (@CommRingPresentation R))
  (i : τ (@CommRingPresentationMorphism R A B))
  (p : τ (@CommRingPresentationMorphism R B C))
  (chain : τ (@CommRingFreydChainPair R A B C i p))
  (H : τ (@CommRingFreydWitnessedHomologyAt R W A B C i p chain))
  (monic : τ (@CommRingFreydMonomorphismWitness R W A B i))
  (epic : τ (@CommRingFreydEpimorphismWitness R B C p))
  (exact : τ (@CommRingFreydExactnessAt R W A B C i p chain H))
  ⊢ @comm_ring_freyd_short_exact_row_chain R W A B C i p (@comm_ring_freyd_short_exact_row_intro R W A B C i p chain H monic epic exact)
  ≡ chain;

assert
  (R : τ CommRing)
  (W : τ (@HasComputationalWeakKernels
    (@CommRingFiniteFree_cat R) (@comm_ring_finite_free_preadditive R)))
  (A B C : τ (@CommRingPresentation R))
  (i : τ (@CommRingPresentationMorphism R A B))
  (p : τ (@CommRingPresentationMorphism R B C))
  (chain : τ (@CommRingFreydChainPair R A B C i p))
  (H : τ (@CommRingFreydWitnessedHomologyAt R W A B C i p chain))
  (monic : τ (@CommRingFreydMonomorphismWitness R W A B i))
  (epic : τ (@CommRingFreydEpimorphismWitness R B C p))
  (exact : τ (@CommRingFreydExactnessAt R W A B C i p chain H))
  ⊢ @comm_ring_freyd_short_exact_row_homology R W A B C i p (@comm_ring_freyd_short_exact_row_intro R W A B C i p chain H monic epic exact)
  ≡ H;

assert
  (R : τ CommRing)
  (W : τ (@HasComputationalWeakKernels
    (@CommRingFiniteFree_cat R) (@comm_ring_finite_free_preadditive R)))
  (A B C : τ (@CommRingPresentation R))
  (i : τ (@CommRingPresentationMorphism R A B))
  (p : τ (@CommRingPresentationMorphism R B C))
  (chain : τ (@CommRingFreydChainPair R A B C i p))
  (H : τ (@CommRingFreydWitnessedHomologyAt R W A B C i p chain))
  (monic : τ (@CommRingFreydMonomorphismWitness R W A B i))
  (epic : τ (@CommRingFreydEpimorphismWitness R B C p))
  (exact : τ (@CommRingFreydExactnessAt R W A B C i p chain H))
  ⊢ @comm_ring_freyd_short_exact_row_monic R W A B C i p (@comm_ring_freyd_short_exact_row_intro R W A B C i p chain H monic epic exact)
  ≡ monic;

assert
  (R : τ CommRing)
  (W : τ (@HasComputationalWeakKernels
    (@CommRingFiniteFree_cat R) (@comm_ring_finite_free_preadditive R)))
  (A B C : τ (@CommRingPresentation R))
  (i : τ (@CommRingPresentationMorphism R A B))
  (p : τ (@CommRingPresentationMorphism R B C))
  (chain : τ (@CommRingFreydChainPair R A B C i p))
  (H : τ (@CommRingFreydWitnessedHomologyAt R W A B C i p chain))
  (monic : τ (@CommRingFreydMonomorphismWitness R W A B i))
  (epic : τ (@CommRingFreydEpimorphismWitness R B C p))
  (exact : τ (@CommRingFreydExactnessAt R W A B C i p chain H))
  ⊢ @comm_ring_freyd_short_exact_row_epic R W A B C i p (@comm_ring_freyd_short_exact_row_intro R W A B C i p chain H monic epic exact)
  ≡ epic;

assert
  (R : τ CommRing)
  (W : τ (@HasComputationalWeakKernels
    (@CommRingFiniteFree_cat R) (@comm_ring_finite_free_preadditive R)))
  (A B C : τ (@CommRingPresentation R))
  (i : τ (@CommRingPresentationMorphism R A B))
  (p : τ (@CommRingPresentationMorphism R B C))
  (chain : τ (@CommRingFreydChainPair R A B C i p))
  (H : τ (@CommRingFreydWitnessedHomologyAt R W A B C i p chain))
  (monic : τ (@CommRingFreydMonomorphismWitness R W A B i))
  (epic : τ (@CommRingFreydEpimorphismWitness R B C p))
  (exact : τ (@CommRingFreydExactnessAt R W A B C i p chain H))
  ⊢ @comm_ring_freyd_short_exact_row_exact R W A B C i p (@comm_ring_freyd_short_exact_row_intro R W A B C i p chain H monic epic exact)
  ≡ exact;

assertnot
  (R : τ CommRing)
  (W : τ (@HasComputationalWeakKernels
    (@CommRingFiniteFree_cat R) (@comm_ring_finite_free_preadditive R)))
  (A B C : τ (@CommRingPresentation R))
  (i : τ (@CommRingPresentationMorphism R A B))
  (p : τ (@CommRingPresentationMorphism R B C))
  (chain : τ (@CommRingFreydChainPair R A B C i p))
  (H : τ (@CommRingFreydWitnessedHomologyAt R W A B C i p chain))
  (monic : τ (@CommRingFreydMonomorphismWitness R W A B i))
  (epic : τ (@CommRingFreydEpimorphismWitness R B C p))
  (exact : τ (@CommRingFreydExactnessAt R W A B C i p chain H))
  (K : τ (@CommRingFreydWitnessedHomologyAt R W A B C i p chain))
  ⊢ @comm_ring_freyd_short_exact_row_exact R W A B C i p (@comm_ring_freyd_short_exact_row_intro R W A B C i p chain H monic epic exact)
  : τ (@CommRingFreydExactnessAt R W A B C i p chain K);
