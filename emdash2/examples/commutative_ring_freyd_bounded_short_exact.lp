/* Actual-map-indexed rows, recursion, whole projections, and negative owner guard. */
require open emdash.emdash3_2_commutative_algebra_freyd_bounded_short_exact;

assert
  (R : τ CommRing)
  (W : τ (@HasComputationalWeakKernels
    (@CommRingFiniteFree_cat R) (@comm_ring_finite_free_preadditive R)))
  (n : τ Nat_grpd)
  (A0 : τ (@CommRingPresentation R))
  (A1 : τ (@CommRingPresentation R))
  (dA : τ (@CommRingPresentationMorphism R A1 A0))
  (tA : τ (@CommRingFreydChainTail R (succ n) A0 A1 dA))
  (B0 : τ (@CommRingPresentation R))
  (B1 : τ (@CommRingPresentation R))
  (dB : τ (@CommRingPresentationMorphism R B1 B0))
  (tB : τ (@CommRingFreydChainTail R (succ n) B0 B1 dB))
  (C0 : τ (@CommRingPresentation R))
  (C1 : τ (@CommRingPresentation R))
  (dC : τ (@CommRingPresentationMorphism R C1 C0))
  (tC : τ (@CommRingFreydChainTail R (succ n) C0 C1 dC))
  (i1 : τ (@CommRingPresentationMorphism R A1 B1))
  (p1 : τ (@CommRingPresentationMorphism R B1 C1))
  (it : τ (@CommRingFreydChainMapTail R (succ n) A0 A1 dA tA B0 B1 dB tB i1))
  (pt : τ (@CommRingFreydChainMapTail R (succ n) B0 B1 dB tB C0 C1 dC tC p1))
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
  ⊢ @comm_ring_freyd_short_exact_tail_row R W n A0 A1 dA tA B0 B1 dB tB C0 C1 dC tC i1 p1 it pt
      (@comm_ring_freyd_short_exact_tail_cons R W n A0 A1 dA tA B0 B1 dB tB C0 C1 dC tC i1 p1 it pt row rest)
  ≡ row;

assert
  (R : τ CommRing)
  (W : τ (@HasComputationalWeakKernels
    (@CommRingFiniteFree_cat R) (@comm_ring_finite_free_preadditive R)))
  (n : τ Nat_grpd)
  (A0 : τ (@CommRingPresentation R))
  (A1 : τ (@CommRingPresentation R))
  (dA : τ (@CommRingPresentationMorphism R A1 A0))
  (tA : τ (@CommRingFreydChainTail R (succ n) A0 A1 dA))
  (B0 : τ (@CommRingPresentation R))
  (B1 : τ (@CommRingPresentation R))
  (dB : τ (@CommRingPresentationMorphism R B1 B0))
  (tB : τ (@CommRingFreydChainTail R (succ n) B0 B1 dB))
  (C0 : τ (@CommRingPresentation R))
  (C1 : τ (@CommRingPresentation R))
  (dC : τ (@CommRingPresentationMorphism R C1 C0))
  (tC : τ (@CommRingFreydChainTail R (succ n) C0 C1 dC))
  (i1 : τ (@CommRingPresentationMorphism R A1 B1))
  (p1 : τ (@CommRingPresentationMorphism R B1 C1))
  (it : τ (@CommRingFreydChainMapTail R (succ n) A0 A1 dA tA B0 B1 dB tB i1))
  (pt : τ (@CommRingFreydChainMapTail R (succ n) B0 B1 dB tB C0 C1 dC tC p1))
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
  ⊢ @comm_ring_freyd_short_exact_tail_rest R W n A0 A1 dA tA B0 B1 dB tB C0 C1 dC tC i1 p1 it pt
      (@comm_ring_freyd_short_exact_tail_cons R W n A0 A1 dA tA B0 B1 dB tB C0 C1 dC tC i1 p1 it pt row rest)
  ≡ rest;

assert
  (R : τ CommRing)
  (W : τ (@HasComputationalWeakKernels
    (@CommRingFiniteFree_cat R) (@comm_ring_finite_free_preadditive R)))
  (n : τ Nat_grpd)
  (A : τ (@CommRingFreydBoundedComplex R (succ n)))
  (B : τ (@CommRingFreydBoundedComplex R (succ n)))
  (C : τ (@CommRingFreydBoundedComplex R (succ n)))
  (i : τ (@CommRingFreydBoundedChainMap R (succ n) A B))
  (p : τ (@CommRingFreydBoundedChainMap R (succ n) B C))
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
  ⊢ @comm_ring_freyd_bounded_short_exact_rows_row0 R W n A B C i p
      (@comm_ring_freyd_bounded_short_exact_rows_succ R W n A B C i p row0 row1 tail)
  ≡ row0;

assert
  (R : τ CommRing)
  (W : τ (@HasComputationalWeakKernels
    (@CommRingFiniteFree_cat R) (@comm_ring_finite_free_preadditive R)))
  (n : τ Nat_grpd)
  (A : τ (@CommRingFreydBoundedComplex R (succ n)))
  (B : τ (@CommRingFreydBoundedComplex R (succ n)))
  (C : τ (@CommRingFreydBoundedComplex R (succ n)))
  (i : τ (@CommRingFreydBoundedChainMap R (succ n) A B))
  (p : τ (@CommRingFreydBoundedChainMap R (succ n) B C))
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
  ⊢ @comm_ring_freyd_bounded_short_exact_rows_row1 R W n A B C i p
      (@comm_ring_freyd_bounded_short_exact_rows_succ R W n A B C i p row0 row1 tail)
  ≡ row1;

assert
  (R : τ CommRing)
  (W : τ (@HasComputationalWeakKernels
    (@CommRingFiniteFree_cat R) (@comm_ring_finite_free_preadditive R)))
  (n : τ Nat_grpd)
  (A : τ (@CommRingFreydBoundedComplex R (succ n)))
  (B : τ (@CommRingFreydBoundedComplex R (succ n)))
  (C : τ (@CommRingFreydBoundedComplex R (succ n)))
  (i : τ (@CommRingFreydBoundedChainMap R (succ n) A B))
  (p : τ (@CommRingFreydBoundedChainMap R (succ n) B C))
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
  ⊢ @comm_ring_freyd_bounded_short_exact_rows_tail R W n A B C i p
      (@comm_ring_freyd_bounded_short_exact_rows_succ R W n A B C i p row0 row1 tail)
  ≡ tail;

assert
  (R : τ CommRing)
  (W : τ (@HasComputationalWeakKernels
    (@CommRingFiniteFree_cat R) (@comm_ring_finite_free_preadditive R)))
  (length : τ Nat_grpd)
  (A : τ (@CommRingFreydBoundedComplex R length))
  (B : τ (@CommRingFreydBoundedComplex R length))
  (C : τ (@CommRingFreydBoundedComplex R length))
  (i : τ (@CommRingFreydBoundedChainMap R length A B))
  (p : τ (@CommRingFreydBoundedChainMap R length B C))
  (rows : τ (@CommRingFreydBoundedShortExactRows R W length A B C i p))
  ⊢ @comm_ring_freyd_bounded_short_exact_sequence_inclusion R W length A B C (@comm_ring_freyd_bounded_short_exact_sequence_intro R W length A B C i p rows)
  ≡ i;

assert
  (R : τ CommRing)
  (W : τ (@HasComputationalWeakKernels
    (@CommRingFiniteFree_cat R) (@comm_ring_finite_free_preadditive R)))
  (length : τ Nat_grpd)
  (A : τ (@CommRingFreydBoundedComplex R length))
  (B : τ (@CommRingFreydBoundedComplex R length))
  (C : τ (@CommRingFreydBoundedComplex R length))
  (i : τ (@CommRingFreydBoundedChainMap R length A B))
  (p : τ (@CommRingFreydBoundedChainMap R length B C))
  (rows : τ (@CommRingFreydBoundedShortExactRows R W length A B C i p))
  ⊢ @comm_ring_freyd_bounded_short_exact_sequence_projection R W length A B C (@comm_ring_freyd_bounded_short_exact_sequence_intro R W length A B C i p rows)
  ≡ p;

assert
  (R : τ CommRing)
  (W : τ (@HasComputationalWeakKernels
    (@CommRingFiniteFree_cat R) (@comm_ring_finite_free_preadditive R)))
  (length : τ Nat_grpd)
  (A : τ (@CommRingFreydBoundedComplex R length))
  (B : τ (@CommRingFreydBoundedComplex R length))
  (C : τ (@CommRingFreydBoundedComplex R length))
  (i : τ (@CommRingFreydBoundedChainMap R length A B))
  (p : τ (@CommRingFreydBoundedChainMap R length B C))
  (rows : τ (@CommRingFreydBoundedShortExactRows R W length A B C i p))
  ⊢ @comm_ring_freyd_bounded_short_exact_sequence_rows R W length A B C (@comm_ring_freyd_bounded_short_exact_sequence_intro R W length A B C i p rows)
  ≡ rows;

assertnot
  (R : τ CommRing)
  (W : τ (@HasComputationalWeakKernels
    (@CommRingFiniteFree_cat R) (@comm_ring_finite_free_preadditive R)))
  (length : τ Nat_grpd)
  (A : τ (@CommRingFreydBoundedComplex R length))
  (B : τ (@CommRingFreydBoundedComplex R length))
  (C : τ (@CommRingFreydBoundedComplex R length))
  (i : τ (@CommRingFreydBoundedChainMap R length A B))
  (p : τ (@CommRingFreydBoundedChainMap R length B C))
  (rows : τ (@CommRingFreydBoundedShortExactRows R W length A B C i p))
  (j : τ (@CommRingFreydBoundedChainMap R length A B))
  ⊢ rows : τ (@CommRingFreydBoundedShortExactRows R W length A B C j p);

assert
  (R : τ CommRing)
  (W : τ (@HasComputationalWeakKernels
    (@CommRingFiniteFree_cat R) (@comm_ring_finite_free_preadditive R)))
  (A : τ (@CommRingFreydBoundedComplex R zero))
  (B : τ (@CommRingFreydBoundedComplex R zero))
  (C : τ (@CommRingFreydBoundedComplex R zero))
  (i : τ (@CommRingFreydBoundedChainMap R zero A B))
  (p : τ (@CommRingFreydBoundedChainMap R zero B C))
  (row : τ (@CommRingFreydShortExactRow R W A B C i p))
  ⊢ @comm_ring_freyd_bounded_short_exact_rows_zero R W A B C i p row ≡ row;

assert
  (R : τ CommRing)
  (W : τ (@HasComputationalWeakKernels
    (@CommRingFiniteFree_cat R) (@comm_ring_finite_free_preadditive R)))
  (A0 : τ (@CommRingPresentation R))
  (A1 : τ (@CommRingPresentation R))
  (dA : τ (@CommRingPresentationMorphism R A1 A0))
  (tA : τ (@CommRingFreydChainTail R zero A0 A1 dA))
  (B0 : τ (@CommRingPresentation R))
  (B1 : τ (@CommRingPresentation R))
  (dB : τ (@CommRingPresentationMorphism R B1 B0))
  (tB : τ (@CommRingFreydChainTail R zero B0 B1 dB))
  (C0 : τ (@CommRingPresentation R))
  (C1 : τ (@CommRingPresentation R))
  (dC : τ (@CommRingPresentationMorphism R C1 C0))
  (tC : τ (@CommRingFreydChainTail R zero C0 C1 dC))
  (i1 : τ (@CommRingPresentationMorphism R A1 B1))
  (p1 : τ (@CommRingPresentationMorphism R B1 C1))
  (it : τ (@CommRingFreydChainMapTail R zero A0 A1 dA tA B0 B1 dB tB i1))
  (pt : τ (@CommRingFreydChainMapTail R zero B0 B1 dB tB C0 C1 dC tC p1))
  ⊢ @comm_ring_freyd_short_exact_tail_nil R W A0 A1 dA tA B0 B1 dB tB C0 C1 dC tC i1 p1 it pt ≡ tt;
