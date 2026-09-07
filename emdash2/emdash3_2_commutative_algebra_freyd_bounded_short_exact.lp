/*
  Degreewise effective exactness over three existing bounded Freyd complexes.

  The predicate follows the actual two bounded chain maps. Each retained row
  uses their projected components; no square or morphism is reconstructed.
  This stores explicit witnesses, not a closed formal exactness decision.
*/

require open emdash.emdash3_2_commutative_algebra_freyd_bounded_chain_maps;
require open emdash.emdash3_2_commutative_algebra_freyd_short_exact_rows;

// Evidence for all degrees strictly above the current three terms.
symbol CommRingFreydShortExactTail
  [R : τ CommRing]
  [W : τ (@HasComputationalWeakKernels
    (@CommRingFiniteFree_cat R) (@comm_ring_finite_free_preadditive R))]
  (length : τ Nat_grpd)
  (A0 : τ (@CommRingPresentation R))
  (A1 : τ (@CommRingPresentation R))
  (dA : τ (@CommRingPresentationMorphism R A1 A0))
  (tA : τ (@CommRingFreydChainTail R length A0 A1 dA))
  (B0 : τ (@CommRingPresentation R))
  (B1 : τ (@CommRingPresentation R))
  (dB : τ (@CommRingPresentationMorphism R B1 B0))
  (tB : τ (@CommRingFreydChainTail R length B0 B1 dB))
  (C0 : τ (@CommRingPresentation R))
  (C1 : τ (@CommRingPresentation R))
  (dC : τ (@CommRingPresentationMorphism R C1 C0))
  (tC : τ (@CommRingFreydChainTail R length C0 C1 dC))
  (i1 : τ (@CommRingPresentationMorphism R A1 B1))
  (p1 : τ (@CommRingPresentationMorphism R B1 C1))
  (it : τ (@CommRingFreydChainMapTail R length A0 A1 dA tA B0 B1 dB tB i1))
  (pt : τ (@CommRingFreydChainMapTail R length B0 B1 dB tB C0 C1 dC tC p1))
  : Grpd
≔ (@nat_elim
    (λ n : τ Nat_grpd,
      @Pi_grpd (@CommRingPresentation R) (λ A0 : τ _,
        @Pi_grpd (@CommRingPresentation R) (λ A1 : τ _,
        @Pi_grpd (@CommRingPresentationMorphism R A1 A0) (λ dA : τ _,
        @Pi_grpd (@CommRingFreydChainTail R n A0 A1 dA) (λ tA : τ _,
        @Pi_grpd (@CommRingPresentation R) (λ B0 : τ _,
        @Pi_grpd (@CommRingPresentation R) (λ B1 : τ _,
        @Pi_grpd (@CommRingPresentationMorphism R B1 B0) (λ dB : τ _,
        @Pi_grpd (@CommRingFreydChainTail R n B0 B1 dB) (λ tB : τ _,
        @Pi_grpd (@CommRingPresentation R) (λ C0 : τ _,
        @Pi_grpd (@CommRingPresentation R) (λ C1 : τ _,
        @Pi_grpd (@CommRingPresentationMorphism R C1 C0) (λ dC : τ _,
        @Pi_grpd (@CommRingFreydChainTail R n C0 C1 dC) (λ tC : τ _,
        @Pi_grpd (@CommRingPresentationMorphism R A1 B1) (λ i1 : τ _,
        @Pi_grpd (@CommRingPresentationMorphism R B1 C1) (λ p1 : τ _,
        @Pi_grpd (@CommRingFreydChainMapTail R n A0 A1 dA tA B0 B1 dB tB i1) (λ it : τ _,
        @Pi_grpd (@CommRingFreydChainMapTail R n B0 B1 dB tB C0 C1 dC tC p1) (λ pt : τ _,
          Grpd_grpd)))))))))))))))))
    (λ A0 : τ (@CommRingPresentation R),
      λ A1 : τ (@CommRingPresentation R),
      λ dA : τ (@CommRingPresentationMorphism R A1 A0),
      λ tA : τ (@CommRingFreydChainTail R zero A0 A1 dA),
      λ B0 : τ (@CommRingPresentation R),
      λ B1 : τ (@CommRingPresentation R),
      λ dB : τ (@CommRingPresentationMorphism R B1 B0),
      λ tB : τ (@CommRingFreydChainTail R zero B0 B1 dB),
      λ C0 : τ (@CommRingPresentation R),
      λ C1 : τ (@CommRingPresentation R),
      λ dC : τ (@CommRingPresentationMorphism R C1 C0),
      λ tC : τ (@CommRingFreydChainTail R zero C0 C1 dC),
      λ i1 : τ (@CommRingPresentationMorphism R A1 B1),
      λ p1 : τ (@CommRingPresentationMorphism R B1 C1),
      λ it : τ (@CommRingFreydChainMapTail R zero A0 A1 dA tA B0 B1 dB tB i1),
      λ pt : τ (@CommRingFreydChainMapTail R zero B0 B1 dB tB C0 C1 dC tC p1),
      Unit_grpd)
    (λ n : τ Nat_grpd, λ rec : τ _,
      λ A0 : τ (@CommRingPresentation R),
      λ A1 : τ (@CommRingPresentation R),
      λ dA : τ (@CommRingPresentationMorphism R A1 A0),
      λ tA : τ (@CommRingFreydChainTail R (succ n) A0 A1 dA),
      λ B0 : τ (@CommRingPresentation R),
      λ B1 : τ (@CommRingPresentation R),
      λ dB : τ (@CommRingPresentationMorphism R B1 B0),
      λ tB : τ (@CommRingFreydChainTail R (succ n) B0 B1 dB),
      λ C0 : τ (@CommRingPresentation R),
      λ C1 : τ (@CommRingPresentation R),
      λ dC : τ (@CommRingPresentationMorphism R C1 C0),
      λ tC : τ (@CommRingFreydChainTail R (succ n) C0 C1 dC),
      λ i1 : τ (@CommRingPresentationMorphism R A1 B1),
      λ p1 : τ (@CommRingPresentationMorphism R B1 C1),
      λ it : τ (@CommRingFreydChainMapTail R (succ n) A0 A1 dA tA B0 B1 dB tB i1),
      λ pt : τ (@CommRingFreydChainMapTail R (succ n) B0 B1 dB tB C0 C1 dC tC p1),
      @Product_grpd (@CommRingFreydShortExactRow R W
      (@comm_ring_freyd_chain_tail_next R n A0 A1 dA tA)
        (@comm_ring_freyd_chain_tail_next R n B0 B1 dB tB)
        (@comm_ring_freyd_chain_tail_next R n C0 C1 dC tC)
      (@comm_ring_freyd_chain_map_tail_next_map R n A0 A1 dA tA B0 B1 dB tB i1 it)
        (@comm_ring_freyd_chain_map_tail_next_map R n B0 B1 dB tB C0 C1 dC tC p1 pt))
        (rec A1 (@comm_ring_freyd_chain_tail_next R n A0 A1 dA tA)
          (@comm_ring_freyd_chain_tail_differential R n A0 A1 dA tA)
          (@comm_ring_freyd_chain_tail_rest R n A0 A1 dA tA)
      B1 (@comm_ring_freyd_chain_tail_next R n B0 B1 dB tB)
        (@comm_ring_freyd_chain_tail_differential R n B0 B1 dB tB)
        (@comm_ring_freyd_chain_tail_rest R n B0 B1 dB tB)
      C1 (@comm_ring_freyd_chain_tail_next R n C0 C1 dC tC)
        (@comm_ring_freyd_chain_tail_differential R n C0 C1 dC tC)
        (@comm_ring_freyd_chain_tail_rest R n C0 C1 dC tC)
      (@comm_ring_freyd_chain_map_tail_next_map R n A0 A1 dA tA B0 B1 dB tB i1 it)
        (@comm_ring_freyd_chain_map_tail_next_map R n B0 B1 dB tB C0 C1 dC tC p1 pt)
      (@comm_ring_freyd_chain_map_tail_rest R n A0 A1 dA tA B0 B1 dB tB i1 it)
        (@comm_ring_freyd_chain_map_tail_rest R n B0 B1 dB tB C0 C1 dC tC p1 pt)))
    length) A0 A1 dA tA B0 B1 dB tB C0 C1 dC tC i1 p1 it pt;

// No further degree has no further exactness obligation.
symbol comm_ring_freyd_short_exact_tail_nil
  [R : τ CommRing]
  [W : τ (@HasComputationalWeakKernels
    (@CommRingFiniteFree_cat R) (@comm_ring_finite_free_preadditive R))]
  [A0 : τ (@CommRingPresentation R)]
  [A1 : τ (@CommRingPresentation R)]
  [dA : τ (@CommRingPresentationMorphism R A1 A0)]
  [tA : τ (@CommRingFreydChainTail R zero A0 A1 dA)]
  [B0 : τ (@CommRingPresentation R)]
  [B1 : τ (@CommRingPresentation R)]
  [dB : τ (@CommRingPresentationMorphism R B1 B0)]
  [tB : τ (@CommRingFreydChainTail R zero B0 B1 dB)]
  [C0 : τ (@CommRingPresentation R)]
  [C1 : τ (@CommRingPresentation R)]
  [dC : τ (@CommRingPresentationMorphism R C1 C0)]
  [tC : τ (@CommRingFreydChainTail R zero C0 C1 dC)]
  [i1 : τ (@CommRingPresentationMorphism R A1 B1)]
  [p1 : τ (@CommRingPresentationMorphism R B1 C1)]
  [it : τ (@CommRingFreydChainMapTail R zero A0 A1 dA tA B0 B1 dB tB i1)]
  [pt : τ (@CommRingFreydChainMapTail R zero B0 B1 dB tB C0 C1 dC tC p1)]
  : τ (@CommRingFreydShortExactTail R W zero A0 A1 dA tA B0 B1 dB tB C0 C1 dC tC i1 p1 it pt)
≔ tt;

// Retain the next actual row and the remaining dependent evidence.
symbol comm_ring_freyd_short_exact_tail_cons
  [R : τ CommRing]
  [W : τ (@HasComputationalWeakKernels
    (@CommRingFiniteFree_cat R) (@comm_ring_finite_free_preadditive R))]
  [n : τ Nat_grpd]
  [A0 : τ (@CommRingPresentation R)]
  [A1 : τ (@CommRingPresentation R)]
  [dA : τ (@CommRingPresentationMorphism R A1 A0)]
  [tA : τ (@CommRingFreydChainTail R (succ n) A0 A1 dA)]
  [B0 : τ (@CommRingPresentation R)]
  [B1 : τ (@CommRingPresentation R)]
  [dB : τ (@CommRingPresentationMorphism R B1 B0)]
  [tB : τ (@CommRingFreydChainTail R (succ n) B0 B1 dB)]
  [C0 : τ (@CommRingPresentation R)]
  [C1 : τ (@CommRingPresentation R)]
  [dC : τ (@CommRingPresentationMorphism R C1 C0)]
  [tC : τ (@CommRingFreydChainTail R (succ n) C0 C1 dC)]
  [i1 : τ (@CommRingPresentationMorphism R A1 B1)]
  [p1 : τ (@CommRingPresentationMorphism R B1 C1)]
  [it : τ (@CommRingFreydChainMapTail R (succ n) A0 A1 dA tA B0 B1 dB tB i1)]
  [pt : τ (@CommRingFreydChainMapTail R (succ n) B0 B1 dB tB C0 C1 dC tC p1)]
  (row : τ (@CommRingFreydShortExactRow R W
      (@comm_ring_freyd_chain_tail_next R n A0 A1 dA tA)
        (@comm_ring_freyd_chain_tail_next R n B0 B1 dB tB)
        (@comm_ring_freyd_chain_tail_next R n C0 C1 dC tC)
      (@comm_ring_freyd_chain_map_tail_next_map R n A0 A1 dA tA B0 B1 dB tB i1 it)
        (@comm_ring_freyd_chain_map_tail_next_map R n B0 B1 dB tB C0 C1 dC tC p1 pt)))
  (rest : τ (@CommRingFreydShortExactTail R W n
      A1 (@comm_ring_freyd_chain_tail_next R n A0 A1 dA tA)
        (@comm_ring_freyd_chain_tail_differential R n A0 A1 dA tA)
        (@comm_ring_freyd_chain_tail_rest R n A0 A1 dA tA)
      B1 (@comm_ring_freyd_chain_tail_next R n B0 B1 dB tB)
        (@comm_ring_freyd_chain_tail_differential R n B0 B1 dB tB)
        (@comm_ring_freyd_chain_tail_rest R n B0 B1 dB tB)
      C1 (@comm_ring_freyd_chain_tail_next R n C0 C1 dC tC)
        (@comm_ring_freyd_chain_tail_differential R n C0 C1 dC tC)
        (@comm_ring_freyd_chain_tail_rest R n C0 C1 dC tC)
      (@comm_ring_freyd_chain_map_tail_next_map R n A0 A1 dA tA B0 B1 dB tB i1 it)
        (@comm_ring_freyd_chain_map_tail_next_map R n B0 B1 dB tB C0 C1 dC tC p1 pt)
      (@comm_ring_freyd_chain_map_tail_rest R n A0 A1 dA tA B0 B1 dB tB i1 it)
        (@comm_ring_freyd_chain_map_tail_rest R n B0 B1 dB tB C0 C1 dC tC p1 pt)))
  : τ (@CommRingFreydShortExactTail R W (succ n) A0 A1 dA tA B0 B1 dB tB C0 C1 dC tC i1 p1 it pt)
≔ Product_pair_grpd row rest;

// Observe retained row evidence at the projected component owners.
symbol comm_ring_freyd_short_exact_tail_row
  [R : τ CommRing]
  [W : τ (@HasComputationalWeakKernels
    (@CommRingFiniteFree_cat R) (@comm_ring_finite_free_preadditive R))]
  [n : τ Nat_grpd]
  [A0 : τ (@CommRingPresentation R)]
  [A1 : τ (@CommRingPresentation R)]
  [dA : τ (@CommRingPresentationMorphism R A1 A0)]
  [tA : τ (@CommRingFreydChainTail R (succ n) A0 A1 dA)]
  [B0 : τ (@CommRingPresentation R)]
  [B1 : τ (@CommRingPresentation R)]
  [dB : τ (@CommRingPresentationMorphism R B1 B0)]
  [tB : τ (@CommRingFreydChainTail R (succ n) B0 B1 dB)]
  [C0 : τ (@CommRingPresentation R)]
  [C1 : τ (@CommRingPresentation R)]
  [dC : τ (@CommRingPresentationMorphism R C1 C0)]
  [tC : τ (@CommRingFreydChainTail R (succ n) C0 C1 dC)]
  [i1 : τ (@CommRingPresentationMorphism R A1 B1)]
  [p1 : τ (@CommRingPresentationMorphism R B1 C1)]
  [it : τ (@CommRingFreydChainMapTail R (succ n) A0 A1 dA tA B0 B1 dB tB i1)]
  [pt : τ (@CommRingFreydChainMapTail R (succ n) B0 B1 dB tB C0 C1 dC tC p1)]
  (rows : τ (@CommRingFreydShortExactTail R W (succ n) A0 A1 dA tA B0 B1 dB tB C0 C1 dC tC i1 p1 it pt))
  : τ (@CommRingFreydShortExactRow R W
      (@comm_ring_freyd_chain_tail_next R n A0 A1 dA tA)
        (@comm_ring_freyd_chain_tail_next R n B0 B1 dB tB)
        (@comm_ring_freyd_chain_tail_next R n C0 C1 dC tC)
      (@comm_ring_freyd_chain_map_tail_next_map R n A0 A1 dA tA B0 B1 dB tB i1 it)
        (@comm_ring_freyd_chain_map_tail_next_map R n B0 B1 dB tB C0 C1 dC tC p1 pt))
≔ sigma_Fst rows;

// Observe retained rest evidence at the projected component owners.
symbol comm_ring_freyd_short_exact_tail_rest
  [R : τ CommRing]
  [W : τ (@HasComputationalWeakKernels
    (@CommRingFiniteFree_cat R) (@comm_ring_finite_free_preadditive R))]
  [n : τ Nat_grpd]
  [A0 : τ (@CommRingPresentation R)]
  [A1 : τ (@CommRingPresentation R)]
  [dA : τ (@CommRingPresentationMorphism R A1 A0)]
  [tA : τ (@CommRingFreydChainTail R (succ n) A0 A1 dA)]
  [B0 : τ (@CommRingPresentation R)]
  [B1 : τ (@CommRingPresentation R)]
  [dB : τ (@CommRingPresentationMorphism R B1 B0)]
  [tB : τ (@CommRingFreydChainTail R (succ n) B0 B1 dB)]
  [C0 : τ (@CommRingPresentation R)]
  [C1 : τ (@CommRingPresentation R)]
  [dC : τ (@CommRingPresentationMorphism R C1 C0)]
  [tC : τ (@CommRingFreydChainTail R (succ n) C0 C1 dC)]
  [i1 : τ (@CommRingPresentationMorphism R A1 B1)]
  [p1 : τ (@CommRingPresentationMorphism R B1 C1)]
  [it : τ (@CommRingFreydChainMapTail R (succ n) A0 A1 dA tA B0 B1 dB tB i1)]
  [pt : τ (@CommRingFreydChainMapTail R (succ n) B0 B1 dB tB C0 C1 dC tC p1)]
  (rows : τ (@CommRingFreydShortExactTail R W (succ n) A0 A1 dA tA B0 B1 dB tB C0 C1 dC tC i1 p1 it pt))
  : τ (@CommRingFreydShortExactTail R W n
      A1 (@comm_ring_freyd_chain_tail_next R n A0 A1 dA tA)
        (@comm_ring_freyd_chain_tail_differential R n A0 A1 dA tA)
        (@comm_ring_freyd_chain_tail_rest R n A0 A1 dA tA)
      B1 (@comm_ring_freyd_chain_tail_next R n B0 B1 dB tB)
        (@comm_ring_freyd_chain_tail_differential R n B0 B1 dB tB)
        (@comm_ring_freyd_chain_tail_rest R n B0 B1 dB tB)
      C1 (@comm_ring_freyd_chain_tail_next R n C0 C1 dC tC)
        (@comm_ring_freyd_chain_tail_differential R n C0 C1 dC tC)
        (@comm_ring_freyd_chain_tail_rest R n C0 C1 dC tC)
      (@comm_ring_freyd_chain_map_tail_next_map R n A0 A1 dA tA B0 B1 dB tB i1 it)
        (@comm_ring_freyd_chain_map_tail_next_map R n B0 B1 dB tB C0 C1 dC tC p1 pt)
      (@comm_ring_freyd_chain_map_tail_rest R n A0 A1 dA tA B0 B1 dB tB i1 it)
        (@comm_ring_freyd_chain_map_tail_rest R n B0 B1 dB tB C0 C1 dC tC p1 pt))
≔ sigma_Snd rows;

// One exactness witness at each actual degree of the two given chain maps.
symbol CommRingFreydBoundedShortExactRows
  [R : τ CommRing]
  [W : τ (@HasComputationalWeakKernels
    (@CommRingFiniteFree_cat R) (@comm_ring_finite_free_preadditive R))]
  (length : τ Nat_grpd)
  (A : τ (@CommRingFreydBoundedComplex R length))
  (B : τ (@CommRingFreydBoundedComplex R length))
  (C : τ (@CommRingFreydBoundedComplex R length))
  (i : τ (@CommRingFreydBoundedChainMap R length A B))
  (p : τ (@CommRingFreydBoundedChainMap R length B C))
  : Grpd
≔ (@nat_elim
    (λ n : τ Nat_grpd,
      @Pi_grpd (@CommRingFreydBoundedComplex R n) (λ A : τ _,
        @Pi_grpd (@CommRingFreydBoundedComplex R n) (λ B : τ _,
        @Pi_grpd (@CommRingFreydBoundedComplex R n) (λ C : τ _,
        @Pi_grpd (@CommRingFreydBoundedChainMap R n A B) (λ i : τ _,
        @Pi_grpd (@CommRingFreydBoundedChainMap R n B C) (λ p : τ _,
          Grpd_grpd))))))
    (λ A : τ (@CommRingFreydBoundedComplex R zero),
      λ B : τ (@CommRingFreydBoundedComplex R zero),
      λ C : τ (@CommRingFreydBoundedComplex R zero),
      λ i : τ (@CommRingFreydBoundedChainMap R zero A B),
      λ p : τ (@CommRingFreydBoundedChainMap R zero B C),
      @CommRingFreydShortExactRow R W A B C i p)
    (λ n : τ Nat_grpd, λ _ : τ _,
      λ A : τ (@CommRingFreydBoundedComplex R (succ n)),
      λ B : τ (@CommRingFreydBoundedComplex R (succ n)),
      λ C : τ (@CommRingFreydBoundedComplex R (succ n)),
      λ i : τ (@CommRingFreydBoundedChainMap R (succ n) A B),
      λ p : τ (@CommRingFreydBoundedChainMap R (succ n) B C),
      @Product_grpd (@CommRingFreydShortExactRow R W
      (@comm_ring_freyd_bounded_complex_P0 R n A)
        (@comm_ring_freyd_bounded_complex_P0 R n B)
        (@comm_ring_freyd_bounded_complex_P0 R n C)
      (@comm_ring_freyd_bounded_chain_map_F0 R n A B i) (@comm_ring_freyd_bounded_chain_map_F0 R n B C p))
        (@Product_grpd (@CommRingFreydShortExactRow R W
      (@comm_ring_freyd_bounded_complex_P1 R n A)
        (@comm_ring_freyd_bounded_complex_P1 R n B)
        (@comm_ring_freyd_bounded_complex_P1 R n C)
      (@comm_ring_freyd_bounded_chain_map_F1 R n A B i)
        (@comm_ring_freyd_bounded_chain_map_F1 R n B C p))
        (@CommRingFreydShortExactTail R W n
      (@comm_ring_freyd_bounded_complex_P0 R n A)
        (@comm_ring_freyd_bounded_complex_P1 R n A)
        (@comm_ring_freyd_bounded_complex_d1 R n A)
        (@comm_ring_freyd_bounded_complex_tail R n A)
      (@comm_ring_freyd_bounded_complex_P0 R n B)
        (@comm_ring_freyd_bounded_complex_P1 R n B)
        (@comm_ring_freyd_bounded_complex_d1 R n B)
        (@comm_ring_freyd_bounded_complex_tail R n B)
      (@comm_ring_freyd_bounded_complex_P0 R n C)
        (@comm_ring_freyd_bounded_complex_P1 R n C)
        (@comm_ring_freyd_bounded_complex_d1 R n C)
        (@comm_ring_freyd_bounded_complex_tail R n C)
      (@comm_ring_freyd_bounded_chain_map_F1 R n A B i) (@comm_ring_freyd_bounded_chain_map_F1 R n B C p)
      (@comm_ring_freyd_bounded_chain_map_tail R n A B i) (@comm_ring_freyd_bounded_chain_map_tail R n B C p))))
    length) A B C i p;

// A length-zero sequence has precisely its degree-zero row.
symbol comm_ring_freyd_bounded_short_exact_rows_zero
  [R : τ CommRing]
  [W : τ (@HasComputationalWeakKernels
    (@CommRingFiniteFree_cat R) (@comm_ring_finite_free_preadditive R))]
  [A : τ (@CommRingFreydBoundedComplex R zero)]
  [B : τ (@CommRingFreydBoundedComplex R zero)]
  [C : τ (@CommRingFreydBoundedComplex R zero)]
  [i : τ (@CommRingFreydBoundedChainMap R zero A B)]
  [p : τ (@CommRingFreydBoundedChainMap R zero B C)]
  (row : τ (@CommRingFreydShortExactRow R W A B C i p))
  : τ (@CommRingFreydBoundedShortExactRows R W zero A B C i p)
≔ row;

// Assemble actual degree-zero/one rows and their remaining exact tail.
symbol comm_ring_freyd_bounded_short_exact_rows_succ
  [R : τ CommRing]
  [W : τ (@HasComputationalWeakKernels
    (@CommRingFiniteFree_cat R) (@comm_ring_finite_free_preadditive R))]
  [n : τ Nat_grpd]
  [A : τ (@CommRingFreydBoundedComplex R (succ n))]
  [B : τ (@CommRingFreydBoundedComplex R (succ n))]
  [C : τ (@CommRingFreydBoundedComplex R (succ n))]
  [i : τ (@CommRingFreydBoundedChainMap R (succ n) A B)]
  [p : τ (@CommRingFreydBoundedChainMap R (succ n) B C)]
  (row0 : τ (@CommRingFreydShortExactRow R W
      (@comm_ring_freyd_bounded_complex_P0 R n A)
        (@comm_ring_freyd_bounded_complex_P0 R n B)
        (@comm_ring_freyd_bounded_complex_P0 R n C)
      (@comm_ring_freyd_bounded_chain_map_F0 R n A B i) (@comm_ring_freyd_bounded_chain_map_F0 R n B C p)))
  (row1 : τ (@CommRingFreydShortExactRow R W
      (@comm_ring_freyd_bounded_complex_P1 R n A)
        (@comm_ring_freyd_bounded_complex_P1 R n B)
        (@comm_ring_freyd_bounded_complex_P1 R n C)
      (@comm_ring_freyd_bounded_chain_map_F1 R n A B i) (@comm_ring_freyd_bounded_chain_map_F1 R n B C p)))
  (tail : τ (@CommRingFreydShortExactTail R W n
      (@comm_ring_freyd_bounded_complex_P0 R n A)
        (@comm_ring_freyd_bounded_complex_P1 R n A)
        (@comm_ring_freyd_bounded_complex_d1 R n A)
        (@comm_ring_freyd_bounded_complex_tail R n A)
      (@comm_ring_freyd_bounded_complex_P0 R n B)
        (@comm_ring_freyd_bounded_complex_P1 R n B)
        (@comm_ring_freyd_bounded_complex_d1 R n B)
        (@comm_ring_freyd_bounded_complex_tail R n B)
      (@comm_ring_freyd_bounded_complex_P0 R n C)
        (@comm_ring_freyd_bounded_complex_P1 R n C)
        (@comm_ring_freyd_bounded_complex_d1 R n C)
        (@comm_ring_freyd_bounded_complex_tail R n C)
      (@comm_ring_freyd_bounded_chain_map_F1 R n A B i) (@comm_ring_freyd_bounded_chain_map_F1 R n B C p)
      (@comm_ring_freyd_bounded_chain_map_tail R n A B i) (@comm_ring_freyd_bounded_chain_map_tail R n B C p)))
  : τ (@CommRingFreydBoundedShortExactRows R W (succ n) A B C i p)
≔ Product_pair_grpd row0 (Product_pair_grpd row1 tail);

// Observe row0 at the actual bounded-map components.
symbol comm_ring_freyd_bounded_short_exact_rows_row0
  [R : τ CommRing]
  [W : τ (@HasComputationalWeakKernels
    (@CommRingFiniteFree_cat R) (@comm_ring_finite_free_preadditive R))]
  [n : τ Nat_grpd]
  [A : τ (@CommRingFreydBoundedComplex R (succ n))]
  [B : τ (@CommRingFreydBoundedComplex R (succ n))]
  [C : τ (@CommRingFreydBoundedComplex R (succ n))]
  [i : τ (@CommRingFreydBoundedChainMap R (succ n) A B)]
  [p : τ (@CommRingFreydBoundedChainMap R (succ n) B C)]
  (rows : τ (@CommRingFreydBoundedShortExactRows R W (succ n) A B C i p))
  : τ (@CommRingFreydShortExactRow R W
      (@comm_ring_freyd_bounded_complex_P0 R n A)
        (@comm_ring_freyd_bounded_complex_P0 R n B)
        (@comm_ring_freyd_bounded_complex_P0 R n C)
      (@comm_ring_freyd_bounded_chain_map_F0 R n A B i) (@comm_ring_freyd_bounded_chain_map_F0 R n B C p))
≔ sigma_Fst rows;

// Observe row1 at the actual bounded-map components.
symbol comm_ring_freyd_bounded_short_exact_rows_row1
  [R : τ CommRing]
  [W : τ (@HasComputationalWeakKernels
    (@CommRingFiniteFree_cat R) (@comm_ring_finite_free_preadditive R))]
  [n : τ Nat_grpd]
  [A : τ (@CommRingFreydBoundedComplex R (succ n))]
  [B : τ (@CommRingFreydBoundedComplex R (succ n))]
  [C : τ (@CommRingFreydBoundedComplex R (succ n))]
  [i : τ (@CommRingFreydBoundedChainMap R (succ n) A B)]
  [p : τ (@CommRingFreydBoundedChainMap R (succ n) B C)]
  (rows : τ (@CommRingFreydBoundedShortExactRows R W (succ n) A B C i p))
  : τ (@CommRingFreydShortExactRow R W
      (@comm_ring_freyd_bounded_complex_P1 R n A)
        (@comm_ring_freyd_bounded_complex_P1 R n B)
        (@comm_ring_freyd_bounded_complex_P1 R n C)
      (@comm_ring_freyd_bounded_chain_map_F1 R n A B i) (@comm_ring_freyd_bounded_chain_map_F1 R n B C p))
≔ sigma_Fst (sigma_Snd rows);

// Observe tail at the actual bounded-map components.
symbol comm_ring_freyd_bounded_short_exact_rows_tail
  [R : τ CommRing]
  [W : τ (@HasComputationalWeakKernels
    (@CommRingFiniteFree_cat R) (@comm_ring_finite_free_preadditive R))]
  [n : τ Nat_grpd]
  [A : τ (@CommRingFreydBoundedComplex R (succ n))]
  [B : τ (@CommRingFreydBoundedComplex R (succ n))]
  [C : τ (@CommRingFreydBoundedComplex R (succ n))]
  [i : τ (@CommRingFreydBoundedChainMap R (succ n) A B)]
  [p : τ (@CommRingFreydBoundedChainMap R (succ n) B C)]
  (rows : τ (@CommRingFreydBoundedShortExactRows R W (succ n) A B C i p))
  : τ (@CommRingFreydShortExactTail R W n
      (@comm_ring_freyd_bounded_complex_P0 R n A)
        (@comm_ring_freyd_bounded_complex_P1 R n A)
        (@comm_ring_freyd_bounded_complex_d1 R n A)
        (@comm_ring_freyd_bounded_complex_tail R n A)
      (@comm_ring_freyd_bounded_complex_P0 R n B)
        (@comm_ring_freyd_bounded_complex_P1 R n B)
        (@comm_ring_freyd_bounded_complex_d1 R n B)
        (@comm_ring_freyd_bounded_complex_tail R n B)
      (@comm_ring_freyd_bounded_complex_P0 R n C)
        (@comm_ring_freyd_bounded_complex_P1 R n C)
        (@comm_ring_freyd_bounded_complex_d1 R n C)
        (@comm_ring_freyd_bounded_complex_tail R n C)
      (@comm_ring_freyd_bounded_chain_map_F1 R n A B i) (@comm_ring_freyd_bounded_chain_map_F1 R n B C p)
      (@comm_ring_freyd_bounded_chain_map_tail R n A B i) (@comm_ring_freyd_bounded_chain_map_tail R n B C p))
≔ sigma_Snd (sigma_Snd rows);

// Whole dependent sequence; the evidence belongs to its stored two maps.
symbol CommRingFreydBoundedShortExactSequence
  [R : τ CommRing]
  [W : τ (@HasComputationalWeakKernels
    (@CommRingFiniteFree_cat R) (@comm_ring_finite_free_preadditive R))]
  (length : τ Nat_grpd)
  (A : τ (@CommRingFreydBoundedComplex R length))
  (B : τ (@CommRingFreydBoundedComplex R length))
  (C : τ (@CommRingFreydBoundedComplex R length))
  : Grpd
≔ `Σ_ i : τ (@CommRingFreydBoundedChainMap R length A B),
    `Σ_ p : τ (@CommRingFreydBoundedChainMap R length B C),
      @CommRingFreydBoundedShortExactRows R W length A B C i p;

// Retain the two whole input chain maps, without duplicating their square laws.
symbol comm_ring_freyd_bounded_short_exact_sequence_intro
  [R : τ CommRing]
  [W : τ (@HasComputationalWeakKernels
    (@CommRingFiniteFree_cat R) (@comm_ring_finite_free_preadditive R))]
  [length : τ Nat_grpd]
  [A : τ (@CommRingFreydBoundedComplex R length)]
  [B : τ (@CommRingFreydBoundedComplex R length)]
  [C : τ (@CommRingFreydBoundedComplex R length)]
  (i : τ (@CommRingFreydBoundedChainMap R length A B))
  (p : τ (@CommRingFreydBoundedChainMap R length B C))
  (rows : τ (@CommRingFreydBoundedShortExactRows R W length A B C i p))
  : τ (@CommRingFreydBoundedShortExactSequence R W length A B C)
≔ Struct_sigma i (Struct_sigma p rows);

// Observe the whole retained inclusion.
symbol comm_ring_freyd_bounded_short_exact_sequence_inclusion
  [R : τ CommRing]
  [W : τ (@HasComputationalWeakKernels
    (@CommRingFiniteFree_cat R) (@comm_ring_finite_free_preadditive R))]
  [length : τ Nat_grpd]
  [A : τ (@CommRingFreydBoundedComplex R length)]
  [B : τ (@CommRingFreydBoundedComplex R length)]
  [C : τ (@CommRingFreydBoundedComplex R length)]
  (sequence : τ (@CommRingFreydBoundedShortExactSequence R W length A B C))
  : τ (@CommRingFreydBoundedChainMap R length A B)
≔ sigma_Fst sequence;

// Observe the whole retained projection.
symbol comm_ring_freyd_bounded_short_exact_sequence_projection
  [R : τ CommRing]
  [W : τ (@HasComputationalWeakKernels
    (@CommRingFiniteFree_cat R) (@comm_ring_finite_free_preadditive R))]
  [length : τ Nat_grpd]
  [A : τ (@CommRingFreydBoundedComplex R length)]
  [B : τ (@CommRingFreydBoundedComplex R length)]
  [C : τ (@CommRingFreydBoundedComplex R length)]
  (sequence : τ (@CommRingFreydBoundedShortExactSequence R W length A B C))
  : τ (@CommRingFreydBoundedChainMap R length B C)
≔ sigma_Fst (sigma_Snd sequence);

// Observe the whole retained rows.
symbol comm_ring_freyd_bounded_short_exact_sequence_rows
  [R : τ CommRing]
  [W : τ (@HasComputationalWeakKernels
    (@CommRingFiniteFree_cat R) (@comm_ring_finite_free_preadditive R))]
  [length : τ Nat_grpd]
  [A : τ (@CommRingFreydBoundedComplex R length)]
  [B : τ (@CommRingFreydBoundedComplex R length)]
  [C : τ (@CommRingFreydBoundedComplex R length)]
  (sequence : τ (@CommRingFreydBoundedShortExactSequence R W length A B C))
  : τ (@CommRingFreydBoundedShortExactRows R W length A B C
      (@comm_ring_freyd_bounded_short_exact_sequence_inclusion R W length A B C sequence)
      (@comm_ring_freyd_bounded_short_exact_sequence_projection R W length A B C sequence))
≔ sigma_Snd (sigma_Snd sequence);
