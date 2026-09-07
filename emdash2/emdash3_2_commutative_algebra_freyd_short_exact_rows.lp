/*
  Effective short-exact row data at fixed raw Freyd morphisms.

  Retain the existing adjacent-zero agreement, actual whole witnessed
  homology, and existing mono/epi/exactness witnesses. No quotient decoder,
  closed Abelian-category instance, new exactness notion, rule, or unifier.
*/

require open emdash.emdash3_2_commutative_algebra_freyd_homology;

// Exactness depends on the boundary of this stored homology, not another row.
symbol CommRingFreydShortExactRow
  [R : τ CommRing]
  [W : τ (@HasComputationalWeakKernels
    (@CommRingFiniteFree_cat R) (@comm_ring_finite_free_preadditive R))]
  [A B C : τ (@CommRingPresentation R)]
  (i : τ (@CommRingPresentationMorphism R A B))
  (p : τ (@CommRingPresentationMorphism R B C))
  : Grpd
≔ `Σ_ chain : τ (@CommRingFreydChainPair R A B C i p),
    `Σ_ H : τ (@CommRingFreydWitnessedHomologyAt R W A B C i p chain),
      @Product_grpd (@CommRingFreydMonomorphismWitness R W A B i)
        (@Product_grpd (@CommRingFreydEpimorphismWitness R B C p) (@CommRingFreydExactnessAt R W A B C i p chain H));

// Assembly from explicit effective data computed/adopted at the CAS boundary.
symbol comm_ring_freyd_short_exact_row_intro
  [R : τ CommRing]
  [W : τ (@HasComputationalWeakKernels
    (@CommRingFiniteFree_cat R) (@comm_ring_finite_free_preadditive R))]
  [A B C : τ (@CommRingPresentation R)]
  [i : τ (@CommRingPresentationMorphism R A B)]
  [p : τ (@CommRingPresentationMorphism R B C)]
  (chain : τ (@CommRingFreydChainPair R A B C i p))
  (H : τ (@CommRingFreydWitnessedHomologyAt R W A B C i p chain))
  (monic : τ (@CommRingFreydMonomorphismWitness R W A B i))
  (epic : τ (@CommRingFreydEpimorphismWitness R B C p))
  (exact : τ (@CommRingFreydExactnessAt R W A B C i p chain H))
  : τ (@CommRingFreydShortExactRow R W A B C i p)
≔ Struct_sigma chain (Struct_sigma H
    (Product_pair_grpd monic (Product_pair_grpd epic exact)));

// The retained zero-composite agreement.
symbol comm_ring_freyd_short_exact_row_chain
  [R : τ CommRing]
  [W : τ (@HasComputationalWeakKernels
    (@CommRingFiniteFree_cat R) (@comm_ring_finite_free_preadditive R))]
  [A B C : τ (@CommRingPresentation R)]
  [i : τ (@CommRingPresentationMorphism R A B)]
  [p : τ (@CommRingPresentationMorphism R B C)]
  (row : τ (@CommRingFreydShortExactRow R W A B C i p))
  : τ (@CommRingFreydChainPair R A B C i p)
≔ sigma_Fst row;

// The actual whole one-degree homology.
symbol comm_ring_freyd_short_exact_row_homology
  [R : τ CommRing]
  [W : τ (@HasComputationalWeakKernels
    (@CommRingFiniteFree_cat R) (@comm_ring_finite_free_preadditive R))]
  [A B C : τ (@CommRingPresentation R)]
  [i : τ (@CommRingPresentationMorphism R A B)]
  [p : τ (@CommRingPresentationMorphism R B C)]
  (row : τ (@CommRingFreydShortExactRow R W A B C i p))
  : τ (@CommRingFreydWitnessedHomologyAt R W A B C i p (@comm_ring_freyd_short_exact_row_chain R W A B C i p row))
≔ sigma_Fst (sigma_Snd row);

// Incoming monomorphism evidence.
symbol comm_ring_freyd_short_exact_row_monic
  [R : τ CommRing]
  [W : τ (@HasComputationalWeakKernels
    (@CommRingFiniteFree_cat R) (@comm_ring_finite_free_preadditive R))]
  [A B C : τ (@CommRingPresentation R)]
  [i : τ (@CommRingPresentationMorphism R A B)]
  [p : τ (@CommRingPresentationMorphism R B C)]
  (row : τ (@CommRingFreydShortExactRow R W A B C i p))
  : τ (@CommRingFreydMonomorphismWitness R W A B i)
≔ sigma_Fst (sigma_Snd (sigma_Snd row));

// Outgoing epimorphism evidence.
symbol comm_ring_freyd_short_exact_row_epic
  [R : τ CommRing]
  [W : τ (@HasComputationalWeakKernels
    (@CommRingFiniteFree_cat R) (@comm_ring_finite_free_preadditive R))]
  [A B C : τ (@CommRingPresentation R)]
  [i : τ (@CommRingPresentationMorphism R A B)]
  [p : τ (@CommRingPresentationMorphism R B C)]
  (row : τ (@CommRingFreydShortExactRow R W A B C i p))
  : τ (@CommRingFreydEpimorphismWitness R B C p)
≔ sigma_Fst (sigma_Snd (sigma_Snd (sigma_Snd row)));

// Exactness of the actual stored boundary.
symbol comm_ring_freyd_short_exact_row_exact
  [R : τ CommRing]
  [W : τ (@HasComputationalWeakKernels
    (@CommRingFiniteFree_cat R) (@comm_ring_finite_free_preadditive R))]
  [A B C : τ (@CommRingPresentation R)]
  [i : τ (@CommRingPresentationMorphism R A B)]
  [p : τ (@CommRingPresentationMorphism R B C)]
  (row : τ (@CommRingFreydShortExactRow R W A B C i p))
  : τ (@CommRingFreydExactnessAt R W A B C i p (@comm_ring_freyd_short_exact_row_chain R W A B C i p row)
    (@comm_ring_freyd_short_exact_row_homology R W A B C i p row))
≔ sigma_Snd (sigma_Snd (sigma_Snd (sigma_Snd row)));
