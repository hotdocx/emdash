/*
  Whole bounded complexes of finite free modules over one commutative ring.

  A boundary-indexed recursive tail internalizes every next rank,
  differential, genuine adjacent-zero law, and remaining tail. Length zero is
  one free-module rank. Positive length stores rank0, rank1, d1, then a tail;
  no redundant 0 o d1 law is imposed. This is a complex presentation, not a
  quotient-module, exactness, homology, or formal category construction.
*/

require open emdash.emdash3_2_commutative_algebra_presentations;

symbol CommRingFreeChainTail
  (R : τ CommRing)
  (length below current : τ Nat_grpd)
  (boundary : τ (@CommRingMatrix R below current))
  : Grpd
≔ (@nat_elim
    (λ _ : τ Nat_grpd,
      @Pi_grpd Nat_grpd
        (λ below0 : τ Nat_grpd,
          @Pi_grpd Nat_grpd
            (λ current0 : τ Nat_grpd,
              @Function_grpd
                (@CommRingMatrix R below0 current0)
                Grpd_grpd)))
    (λ below0 : τ Nat_grpd,
      λ current0 : τ Nat_grpd,
      λ _ : τ (@CommRingMatrix R below0 current0),
        Unit_grpd)
    (λ length0 : τ Nat_grpd,
      λ rec : τ (@Pi_grpd Nat_grpd
        (λ below0 : τ Nat_grpd,
          @Pi_grpd Nat_grpd
            (λ current0 : τ Nat_grpd,
              @Function_grpd
                (@CommRingMatrix R below0 current0)
                Grpd_grpd))),
      λ below0 : τ Nat_grpd,
      λ current0 : τ Nat_grpd,
      λ boundary0 : τ (@CommRingMatrix R below0 current0),
        `Σ_ next : τ Nat_grpd,
          `Σ_ differential : τ (@CommRingMatrix R current0 next),
            @Product_grpd
              (@CommRingMatrixCompositeZero R
                below0 current0 next boundary0 differential)
              (rec current0 next differential))
    length) below current boundary;

symbol comm_ring_free_chain_tail_nil
  [R : τ CommRing]
  [below current : τ Nat_grpd]
  [boundary : τ (@CommRingMatrix R below current)]
  : τ (@CommRingFreeChainTail R zero below current boundary)
≔ tt;

symbol comm_ring_free_chain_tail_cons
  [R : τ CommRing]
  [length below current : τ Nat_grpd]
  [boundary : τ (@CommRingMatrix R below current)]
  (next : τ Nat_grpd)
  (differential : τ (@CommRingMatrix R current next))
  (law : τ (@CommRingMatrixCompositeZero R
      below current next boundary differential))
  (rest : τ (@CommRingFreeChainTail R
      length current next differential))
  : τ (@CommRingFreeChainTail R
      (succ length) below current boundary)
≔ @Struct_sigma
    Nat_grpd
    (λ next0 : τ Nat_grpd,
      `Σ_ differential0 : τ (@CommRingMatrix R current next0),
        @Product_grpd
          (@CommRingMatrixCompositeZero R
            below current next0 boundary differential0)
          (@CommRingFreeChainTail R
            length current next0 differential0))
    next
    (@Struct_sigma
      (@CommRingMatrix R current next)
      (λ differential0 : τ (@CommRingMatrix R current next),
        @Product_grpd
          (@CommRingMatrixCompositeZero R
            below current next boundary differential0)
          (@CommRingFreeChainTail R
            length current next differential0))
      differential
      (@Product_pair_grpd
        (@CommRingMatrixCompositeZero R
          below current next boundary differential)
        (@CommRingFreeChainTail R
          length current next differential)
        law rest));

symbol comm_ring_free_chain_tail_next_rank
  [R : τ CommRing]
  [length below current : τ Nat_grpd]
  [boundary : τ (@CommRingMatrix R below current)]
  (tail : τ (@CommRingFreeChainTail R
      (succ length) below current boundary))
  : τ Nat_grpd
≔ sigma_Fst tail;

symbol comm_ring_free_chain_tail_differential
  [R : τ CommRing]
  [length below current : τ Nat_grpd]
  [boundary : τ (@CommRingMatrix R below current)]
  (tail : τ (@CommRingFreeChainTail R
      (succ length) below current boundary))
  : τ (@CommRingMatrix R current
      (@comm_ring_free_chain_tail_next_rank R
        length below current boundary tail))
≔ sigma_Fst (sigma_Snd tail);

symbol comm_ring_free_chain_tail_law
  [R : τ CommRing]
  [length below current : τ Nat_grpd]
  [boundary : τ (@CommRingMatrix R below current)]
  (tail : τ (@CommRingFreeChainTail R
      (succ length) below current boundary))
  : τ (@CommRingMatrixCompositeZero R
      below current
      (@comm_ring_free_chain_tail_next_rank R
        length below current boundary tail)
      boundary
      (@comm_ring_free_chain_tail_differential R
        length below current boundary tail))
≔ sigma_Fst (sigma_Snd (sigma_Snd tail));

symbol comm_ring_free_chain_tail_rest
  [R : τ CommRing]
  [length below current : τ Nat_grpd]
  [boundary : τ (@CommRingMatrix R below current)]
  (tail : τ (@CommRingFreeChainTail R
      (succ length) below current boundary))
  : τ (@CommRingFreeChainTail R
      length current
      (@comm_ring_free_chain_tail_next_rank R
        length below current boundary tail)
      (@comm_ring_free_chain_tail_differential R
        length below current boundary tail))
≔ sigma_Snd (sigma_Snd (sigma_Snd tail));

symbol CommRingBoundedFreeComplex
  (R : τ CommRing)
  (length : τ Nat_grpd)
  : Grpd
≔ @nat_elim
    (λ _ : τ Nat_grpd, Obj Grpd_cat)
    Nat_grpd
    (λ tailLength : τ Nat_grpd,
      λ _ : Grpd,
        `Σ_ rank0 : τ Nat_grpd,
          `Σ_ rank1 : τ Nat_grpd,
            `Σ_ d1 : τ (@CommRingMatrix R rank0 rank1),
              @CommRingFreeChainTail R
                tailLength rank0 rank1 d1)
    length;

symbol comm_ring_bounded_free_complex_zero
  [R : τ CommRing]
  (rank0 : τ Nat_grpd)
  : τ (@CommRingBoundedFreeComplex R zero)
≔ rank0;

symbol comm_ring_bounded_free_complex_succ
  [R : τ CommRing]
  [tailLength : τ Nat_grpd]
  (rank0 rank1 : τ Nat_grpd)
  (d1 : τ (@CommRingMatrix R rank0 rank1))
  (tail : τ (@CommRingFreeChainTail R
      tailLength rank0 rank1 d1))
  : τ (@CommRingBoundedFreeComplex R (succ tailLength))
≔ @Struct_sigma
    Nat_grpd
    (λ rank00 : τ Nat_grpd,
      `Σ_ rank10 : τ Nat_grpd,
        `Σ_ d10 : τ (@CommRingMatrix R rank00 rank10),
          @CommRingFreeChainTail R
            tailLength rank00 rank10 d10)
    rank0
    (@Struct_sigma
      Nat_grpd
      (λ rank10 : τ Nat_grpd,
        `Σ_ d10 : τ (@CommRingMatrix R rank0 rank10),
          @CommRingFreeChainTail R
            tailLength rank0 rank10 d10)
      rank1
      (@Struct_sigma
        (@CommRingMatrix R rank0 rank1)
        (λ d10 : τ (@CommRingMatrix R rank0 rank1),
          @CommRingFreeChainTail R
            tailLength rank0 rank1 d10)
        d1 tail));

symbol comm_ring_bounded_free_complex_zero_rank
  [R : τ CommRing]
  (C : τ (@CommRingBoundedFreeComplex R zero))
  : τ Nat_grpd
≔ C;

symbol comm_ring_bounded_free_complex_rank0
  [R : τ CommRing]
  [tailLength : τ Nat_grpd]
  (C : τ (@CommRingBoundedFreeComplex R (succ tailLength)))
  : τ Nat_grpd
≔ sigma_Fst C;

symbol comm_ring_bounded_free_complex_rank1
  [R : τ CommRing]
  [tailLength : τ Nat_grpd]
  (C : τ (@CommRingBoundedFreeComplex R (succ tailLength)))
  : τ Nat_grpd
≔ sigma_Fst (sigma_Snd C);

symbol comm_ring_bounded_free_complex_d1
  [R : τ CommRing]
  [tailLength : τ Nat_grpd]
  (C : τ (@CommRingBoundedFreeComplex R (succ tailLength)))
  : τ (@CommRingMatrix R
      (@comm_ring_bounded_free_complex_rank0 R tailLength C)
      (@comm_ring_bounded_free_complex_rank1 R tailLength C))
≔ sigma_Fst (sigma_Snd (sigma_Snd C));

symbol comm_ring_bounded_free_complex_tail
  [R : τ CommRing]
  [tailLength : τ Nat_grpd]
  (C : τ (@CommRingBoundedFreeComplex R (succ tailLength)))
  : τ (@CommRingFreeChainTail R tailLength
      (@comm_ring_bounded_free_complex_rank0 R tailLength C)
      (@comm_ring_bounded_free_complex_rank1 R tailLength C)
      (@comm_ring_bounded_free_complex_d1 R tailLength C))
≔ sigma_Snd (sigma_Snd (sigma_Snd C));
