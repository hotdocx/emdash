/* Reviewer-facing whole bounded chain-map consumer. */

require open emdash.emdash3_2_commutative_algebra_bounded_free_chain_maps;

symbol one_step_complex
  (R : τ CommRing)
  (rank0 rank1 : τ Nat_grpd)
  (d1 : τ (@CommRingMatrix R rank0 rank1))
  : τ (@CommRingBoundedFreeComplex R (succ zero))
≔ @comm_ring_bounded_free_complex_succ R
    zero rank0 rank1 d1
    (@comm_ring_free_chain_tail_nil R rank0 rank1 d1);

symbol one_step_chain_map
  (R : τ CommRing)
  (source0 source1 target0 target1 : τ Nat_grpd)
  (d1 : τ (@CommRingMatrix R source0 source1))
  (e1 : τ (@CommRingMatrix R target0 target1))
  (F0 : τ (@CommRingMatrix R target0 source0))
  (F1 : τ (@CommRingMatrix R target1 source1))
  (law : τ (@CommRingChainMapSquare R
      source0 source1 target0 target1 d1 e1 F0 F1))
  : τ (@CommRingBoundedFreeChainMap R (succ zero)
      (@one_step_complex R source0 source1 d1)
      (@one_step_complex R target0 target1 e1))
≔ @comm_ring_bounded_free_chain_map_succ R zero
    (@one_step_complex R source0 source1 d1)
    (@one_step_complex R target0 target1 e1)
    F0 F1 law
    (@comm_ring_free_chain_map_tail_nil R
      source0 source1 d1
      (@comm_ring_free_chain_tail_nil R source0 source1 d1)
      target0 target1 e1
      (@comm_ring_free_chain_tail_nil R target0 target1 e1)
      F1);

assert
  (R : τ CommRing)
  (source0 source1 target0 target1 : τ Nat_grpd)
  (d1 : τ (@CommRingMatrix R source0 source1))
  (e1 : τ (@CommRingMatrix R target0 target1))
  (F0 : τ (@CommRingMatrix R target0 source0))
  (F1 : τ (@CommRingMatrix R target1 source1))
  (law : τ (@CommRingChainMapSquare R
      source0 source1 target0 target1 d1 e1 F0 F1))
  ⊢ @comm_ring_bounded_free_chain_map_F0 R zero
      (@one_step_complex R source0 source1 d1)
      (@one_step_complex R target0 target1 e1)
      (@one_step_chain_map R
        source0 source1 target0 target1 d1 e1 F0 F1 law)
  ≡ F0;

assert
  (R : τ CommRing)
  (source0 source1 target0 target1 : τ Nat_grpd)
  (d1 : τ (@CommRingMatrix R source0 source1))
  (e1 : τ (@CommRingMatrix R target0 target1))
  (F0 : τ (@CommRingMatrix R target0 source0))
  (F1 : τ (@CommRingMatrix R target1 source1))
  (law : τ (@CommRingChainMapSquare R
      source0 source1 target0 target1 d1 e1 F0 F1))
  ⊢ @comm_ring_bounded_free_chain_map_F1 R zero
      (@one_step_complex R source0 source1 d1)
      (@one_step_complex R target0 target1 e1)
      (@one_step_chain_map R
        source0 source1 target0 target1 d1 e1 F0 F1 law)
  ≡ F1;

assertnot
  (R : τ CommRing)
  (source0 source1 target0 target1 : τ Nat_grpd)
  (d1 : τ (@CommRingMatrix R source0 source1))
  (e1 : τ (@CommRingMatrix R target0 target1))
  (F0 G0 : τ (@CommRingMatrix R target0 source0))
  (F1 : τ (@CommRingMatrix R target1 source1))
  (lawF : τ (@CommRingChainMapSquare R
      source0 source1 target0 target1 d1 e1 F0 F1))
  (lawG : τ (@CommRingChainMapSquare R
      source0 source1 target0 target1 d1 e1 G0 F1))
  ⊢ @comm_ring_bounded_free_chain_map_F0 R zero
      (@one_step_complex R source0 source1 d1)
      (@one_step_complex R target0 target1 e1)
      (@one_step_chain_map R
        source0 source1 target0 target1 d1 e1 F0 F1 lawF)
  ≡ @comm_ring_bounded_free_chain_map_F0 R zero
      (@one_step_complex R source0 source1 d1)
      (@one_step_complex R target0 target1 e1)
      (@one_step_chain_map R
        source0 source1 target0 target1 d1 e1 G0 F1 lawG);
