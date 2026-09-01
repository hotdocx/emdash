/* Reviewer-facing bounded free-complex consumer. */

require open emdash.emdash3_2_commutative_algebra_bounded_free_complexes;

symbol bounded_complex_two_tail
  (R : τ CommRing)
  (rank0 rank1 rank2 : τ Nat_grpd)
  (d1 : τ (@CommRingMatrix R rank0 rank1))
  (d2 : τ (@CommRingMatrix R rank1 rank2))
  (law : τ (@CommRingMatrixCompositeZero R
      rank0 rank1 rank2 d1 d2))
  : τ (@CommRingFreeChainTail R
      (succ zero) rank0 rank1 d1)
≔ @comm_ring_free_chain_tail_cons R
    zero rank0 rank1 d1
    rank2 d2 law
    (@comm_ring_free_chain_tail_nil R rank1 rank2 d2);

symbol bounded_complex_two
  (R : τ CommRing)
  (rank0 rank1 rank2 : τ Nat_grpd)
  (d1 : τ (@CommRingMatrix R rank0 rank1))
  (d2 : τ (@CommRingMatrix R rank1 rank2))
  (law : τ (@CommRingMatrixCompositeZero R
      rank0 rank1 rank2 d1 d2))
  : τ (@CommRingBoundedFreeComplex R (succ (succ zero)))
≔ @comm_ring_bounded_free_complex_succ R
    (succ zero) rank0 rank1 d1
    (@bounded_complex_two_tail R rank0 rank1 rank2 d1 d2 law);

assert
  (R : τ CommRing)
  (rank0 rank1 rank2 : τ Nat_grpd)
  (d1 : τ (@CommRingMatrix R rank0 rank1))
  (d2 : τ (@CommRingMatrix R rank1 rank2))
  (law : τ (@CommRingMatrixCompositeZero R
      rank0 rank1 rank2 d1 d2))
  ⊢ @comm_ring_bounded_free_complex_rank0 R (succ zero)
      (@bounded_complex_two R rank0 rank1 rank2 d1 d2 law)
  ≡ rank0;

assert
  (R : τ CommRing)
  (rank0 rank1 rank2 : τ Nat_grpd)
  (d1 : τ (@CommRingMatrix R rank0 rank1))
  (d2 : τ (@CommRingMatrix R rank1 rank2))
  (law : τ (@CommRingMatrixCompositeZero R
      rank0 rank1 rank2 d1 d2))
  ⊢ @comm_ring_bounded_free_complex_d1 R (succ zero)
      (@bounded_complex_two R rank0 rank1 rank2 d1 d2 law)
  ≡ d1;

assert
  (R : τ CommRing)
  (rank0 rank1 rank2 : τ Nat_grpd)
  (d1 : τ (@CommRingMatrix R rank0 rank1))
  (d2 : τ (@CommRingMatrix R rank1 rank2))
  (law : τ (@CommRingMatrixCompositeZero R
      rank0 rank1 rank2 d1 d2))
  ⊢ @comm_ring_free_chain_tail_next_rank R
      zero rank0 rank1 d1
      (@comm_ring_bounded_free_complex_tail R (succ zero)
        (@bounded_complex_two R rank0 rank1 rank2 d1 d2 law))
  ≡ rank2;

assert
  (R : τ CommRing)
  (rank0 rank1 rank2 : τ Nat_grpd)
  (d1 : τ (@CommRingMatrix R rank0 rank1))
  (d2 : τ (@CommRingMatrix R rank1 rank2))
  (law : τ (@CommRingMatrixCompositeZero R
      rank0 rank1 rank2 d1 d2))
  ⊢ @comm_ring_free_chain_tail_differential R
      zero rank0 rank1 d1
      (@comm_ring_bounded_free_complex_tail R (succ zero)
        (@bounded_complex_two R rank0 rank1 rank2 d1 d2 law))
  ≡ d2;

// Different selected boundary matrices remain runtime data.
assertnot
  (R : τ CommRing)
  (rank0 rank1 : τ Nat_grpd)
  (d e : τ (@CommRingMatrix R rank0 rank1))
  ⊢ @comm_ring_bounded_free_complex_d1 R zero
      (@comm_ring_bounded_free_complex_succ R
        zero rank0 rank1 d
        (@comm_ring_free_chain_tail_nil R rank0 rank1 d))
  ≡ @comm_ring_bounded_free_complex_d1 R zero
      (@comm_ring_bounded_free_complex_succ R
        zero rank0 rank1 e
        (@comm_ring_free_chain_tail_nil R rank0 rank1 e));
