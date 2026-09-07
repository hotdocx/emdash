/* Actual-owner beta and endpoint consumers for bounded Freyd chain maps. */
require open emdash.emdash3_2_commutative_algebra_freyd_bounded_chain_maps;

assert
  (R : τ CommRing)
  (n : τ Nat_grpd)
  (S T : τ (@CommRingFreydBoundedComplex R (succ n)))
  (f0 : τ (@CommRingPresentationMorphism R (@comm_ring_freyd_bounded_complex_P0 R n S) (@comm_ring_freyd_bounded_complex_P0 R n T)))
  (f1 : τ (@CommRingPresentationMorphism R (@comm_ring_freyd_bounded_complex_P1 R n S) (@comm_ring_freyd_bounded_complex_P1 R n T)))
  (law : τ (@CommRingFreydChainMapSquare R (@comm_ring_freyd_bounded_complex_P0 R n S) (@comm_ring_freyd_bounded_complex_P1 R n S) (@comm_ring_freyd_bounded_complex_P0 R n T) (@comm_ring_freyd_bounded_complex_P1 R n T) (@comm_ring_freyd_bounded_complex_d1 R n S) (@comm_ring_freyd_bounded_complex_d1 R n T) f0 f1))
  (tail : τ (@CommRingFreydChainMapTail R n (@comm_ring_freyd_bounded_complex_P0 R n S) (@comm_ring_freyd_bounded_complex_P1 R n S) (@comm_ring_freyd_bounded_complex_d1 R n S) (@comm_ring_freyd_bounded_complex_tail R n S) (@comm_ring_freyd_bounded_complex_P0 R n T) (@comm_ring_freyd_bounded_complex_P1 R n T) (@comm_ring_freyd_bounded_complex_d1 R n T) (@comm_ring_freyd_bounded_complex_tail R n T) f1))
  ⊢ @comm_ring_freyd_bounded_chain_map_F0 R n S T (@comm_ring_freyd_bounded_chain_map_succ R n S T f0 f1 law tail)
  ≡ f0;

assert
  (R : τ CommRing)
  (n : τ Nat_grpd)
  (S T : τ (@CommRingFreydBoundedComplex R (succ n)))
  (f0 : τ (@CommRingPresentationMorphism R (@comm_ring_freyd_bounded_complex_P0 R n S) (@comm_ring_freyd_bounded_complex_P0 R n T)))
  (f1 : τ (@CommRingPresentationMorphism R (@comm_ring_freyd_bounded_complex_P1 R n S) (@comm_ring_freyd_bounded_complex_P1 R n T)))
  (law : τ (@CommRingFreydChainMapSquare R (@comm_ring_freyd_bounded_complex_P0 R n S) (@comm_ring_freyd_bounded_complex_P1 R n S) (@comm_ring_freyd_bounded_complex_P0 R n T) (@comm_ring_freyd_bounded_complex_P1 R n T) (@comm_ring_freyd_bounded_complex_d1 R n S) (@comm_ring_freyd_bounded_complex_d1 R n T) f0 f1))
  (tail : τ (@CommRingFreydChainMapTail R n (@comm_ring_freyd_bounded_complex_P0 R n S) (@comm_ring_freyd_bounded_complex_P1 R n S) (@comm_ring_freyd_bounded_complex_d1 R n S) (@comm_ring_freyd_bounded_complex_tail R n S) (@comm_ring_freyd_bounded_complex_P0 R n T) (@comm_ring_freyd_bounded_complex_P1 R n T) (@comm_ring_freyd_bounded_complex_d1 R n T) (@comm_ring_freyd_bounded_complex_tail R n T) f1))
  ⊢ @comm_ring_freyd_bounded_chain_map_F1 R n S T (@comm_ring_freyd_bounded_chain_map_succ R n S T f0 f1 law tail)
  ≡ f1;

assert
  (R : τ CommRing)
  (n : τ Nat_grpd)
  (S T : τ (@CommRingFreydBoundedComplex R (succ n)))
  (f0 : τ (@CommRingPresentationMorphism R (@comm_ring_freyd_bounded_complex_P0 R n S) (@comm_ring_freyd_bounded_complex_P0 R n T)))
  (f1 : τ (@CommRingPresentationMorphism R (@comm_ring_freyd_bounded_complex_P1 R n S) (@comm_ring_freyd_bounded_complex_P1 R n T)))
  (law : τ (@CommRingFreydChainMapSquare R (@comm_ring_freyd_bounded_complex_P0 R n S) (@comm_ring_freyd_bounded_complex_P1 R n S) (@comm_ring_freyd_bounded_complex_P0 R n T) (@comm_ring_freyd_bounded_complex_P1 R n T) (@comm_ring_freyd_bounded_complex_d1 R n S) (@comm_ring_freyd_bounded_complex_d1 R n T) f0 f1))
  (tail : τ (@CommRingFreydChainMapTail R n (@comm_ring_freyd_bounded_complex_P0 R n S) (@comm_ring_freyd_bounded_complex_P1 R n S) (@comm_ring_freyd_bounded_complex_d1 R n S) (@comm_ring_freyd_bounded_complex_tail R n S) (@comm_ring_freyd_bounded_complex_P0 R n T) (@comm_ring_freyd_bounded_complex_P1 R n T) (@comm_ring_freyd_bounded_complex_d1 R n T) (@comm_ring_freyd_bounded_complex_tail R n T) f1))
  ⊢ @comm_ring_freyd_bounded_chain_map_first_law R n S T (@comm_ring_freyd_bounded_chain_map_succ R n S T f0 f1 law tail)
  ≡ law;

assert
  (R : τ CommRing)
  (n : τ Nat_grpd)
  (S T : τ (@CommRingFreydBoundedComplex R (succ n)))
  (f0 : τ (@CommRingPresentationMorphism R (@comm_ring_freyd_bounded_complex_P0 R n S) (@comm_ring_freyd_bounded_complex_P0 R n T)))
  (f1 : τ (@CommRingPresentationMorphism R (@comm_ring_freyd_bounded_complex_P1 R n S) (@comm_ring_freyd_bounded_complex_P1 R n T)))
  (law : τ (@CommRingFreydChainMapSquare R (@comm_ring_freyd_bounded_complex_P0 R n S) (@comm_ring_freyd_bounded_complex_P1 R n S) (@comm_ring_freyd_bounded_complex_P0 R n T) (@comm_ring_freyd_bounded_complex_P1 R n T) (@comm_ring_freyd_bounded_complex_d1 R n S) (@comm_ring_freyd_bounded_complex_d1 R n T) f0 f1))
  (tail : τ (@CommRingFreydChainMapTail R n (@comm_ring_freyd_bounded_complex_P0 R n S) (@comm_ring_freyd_bounded_complex_P1 R n S) (@comm_ring_freyd_bounded_complex_d1 R n S) (@comm_ring_freyd_bounded_complex_tail R n S) (@comm_ring_freyd_bounded_complex_P0 R n T) (@comm_ring_freyd_bounded_complex_P1 R n T) (@comm_ring_freyd_bounded_complex_d1 R n T) (@comm_ring_freyd_bounded_complex_tail R n T) f1))
  ⊢ @comm_ring_freyd_bounded_chain_map_tail R n S T (@comm_ring_freyd_bounded_chain_map_succ R n S T f0 f1 law tail)
  ≡ tail;

assert
  (R : τ CommRing)
  (S T : τ (@CommRingPresentation R))
  (f : τ (@CommRingPresentationMorphism R S T))
  ⊢ @comm_ring_freyd_bounded_chain_map_zero R S T f ≡ f;

assertnot
  (R : τ CommRing)
  (S T U : τ (@CommRingPresentation R))
  (f : τ (@CommRingPresentationMorphism R S T))
  ⊢ @comm_ring_freyd_bounded_chain_map_zero R S T f
  : τ (@CommRingFreydBoundedChainMap R zero S U);

assert
  (R : τ CommRing)
  (n : τ Nat_grpd)
  (S0 S1 T0 T1 : τ (@CommRingPresentation R))
  (sd : τ (@CommRingPresentationMorphism R S1 S0))
  (td : τ (@CommRingPresentationMorphism R T1 T0))
  (st : τ (@CommRingFreydChainTail R (succ n) S0 S1 sd))
  (tt : τ (@CommRingFreydChainTail R (succ n) T0 T1 td))
  (f0 : τ (@CommRingPresentationMorphism R S0 T0))
  (f1 : τ (@CommRingPresentationMorphism R S1 T1))
  (f2 : τ (@CommRingPresentationMorphism R (@comm_ring_freyd_chain_tail_next R n S0 S1 sd st) (@comm_ring_freyd_chain_tail_next R n T0 T1 td tt)))
  (lower : τ (@CommRingFreydChainMapSquare R S0 S1 T0 T1 sd td f0 f1))
  (upper : τ (@CommRingFreydChainMapSquare R S1 (@comm_ring_freyd_chain_tail_next R n S0 S1 sd st) T1 (@comm_ring_freyd_chain_tail_next R n T0 T1 td tt) (@comm_ring_freyd_chain_tail_differential R n S0 S1 sd st) (@comm_ring_freyd_chain_tail_differential R n T0 T1 td tt) f1 f2))
  (rest : τ (@CommRingFreydChainMapTail R n S1 (@comm_ring_freyd_chain_tail_next R n S0 S1 sd st) (@comm_ring_freyd_chain_tail_differential R n S0 S1 sd st) (@comm_ring_freyd_chain_tail_rest R n S0 S1 sd st) T1 (@comm_ring_freyd_chain_tail_next R n T0 T1 td tt) (@comm_ring_freyd_chain_tail_differential R n T0 T1 td tt) (@comm_ring_freyd_chain_tail_rest R n T0 T1 td tt) f2))
  ⊢ @comm_ring_freyd_chain_map_tail_next_map R n S0 S1 sd st T0 T1 td tt f1 (@comm_ring_freyd_chain_map_tail_cons R n S0 S1 sd st T0 T1 td tt f1 f2 upper rest)
  ≡ f2;

assert
  (R : τ CommRing)
  (n : τ Nat_grpd)
  (S0 S1 T0 T1 : τ (@CommRingPresentation R))
  (sd : τ (@CommRingPresentationMorphism R S1 S0))
  (td : τ (@CommRingPresentationMorphism R T1 T0))
  (st : τ (@CommRingFreydChainTail R (succ n) S0 S1 sd))
  (tt : τ (@CommRingFreydChainTail R (succ n) T0 T1 td))
  (f0 : τ (@CommRingPresentationMorphism R S0 T0))
  (f1 : τ (@CommRingPresentationMorphism R S1 T1))
  (f2 : τ (@CommRingPresentationMorphism R (@comm_ring_freyd_chain_tail_next R n S0 S1 sd st) (@comm_ring_freyd_chain_tail_next R n T0 T1 td tt)))
  (lower : τ (@CommRingFreydChainMapSquare R S0 S1 T0 T1 sd td f0 f1))
  (upper : τ (@CommRingFreydChainMapSquare R S1 (@comm_ring_freyd_chain_tail_next R n S0 S1 sd st) T1 (@comm_ring_freyd_chain_tail_next R n T0 T1 td tt) (@comm_ring_freyd_chain_tail_differential R n S0 S1 sd st) (@comm_ring_freyd_chain_tail_differential R n T0 T1 td tt) f1 f2))
  (rest : τ (@CommRingFreydChainMapTail R n S1 (@comm_ring_freyd_chain_tail_next R n S0 S1 sd st) (@comm_ring_freyd_chain_tail_differential R n S0 S1 sd st) (@comm_ring_freyd_chain_tail_rest R n S0 S1 sd st) T1 (@comm_ring_freyd_chain_tail_next R n T0 T1 td tt) (@comm_ring_freyd_chain_tail_differential R n T0 T1 td tt) (@comm_ring_freyd_chain_tail_rest R n T0 T1 td tt) f2))
  ⊢ @comm_ring_freyd_chain_map_tail_law R n S0 S1 sd st T0 T1 td tt f1 (@comm_ring_freyd_chain_map_tail_cons R n S0 S1 sd st T0 T1 td tt f1 f2 upper rest)
  ≡ upper;

assert
  (R : τ CommRing)
  (n : τ Nat_grpd)
  (S0 S1 T0 T1 : τ (@CommRingPresentation R))
  (sd : τ (@CommRingPresentationMorphism R S1 S0))
  (td : τ (@CommRingPresentationMorphism R T1 T0))
  (st : τ (@CommRingFreydChainTail R (succ n) S0 S1 sd))
  (tt : τ (@CommRingFreydChainTail R (succ n) T0 T1 td))
  (f0 : τ (@CommRingPresentationMorphism R S0 T0))
  (f1 : τ (@CommRingPresentationMorphism R S1 T1))
  (f2 : τ (@CommRingPresentationMorphism R (@comm_ring_freyd_chain_tail_next R n S0 S1 sd st) (@comm_ring_freyd_chain_tail_next R n T0 T1 td tt)))
  (lower : τ (@CommRingFreydChainMapSquare R S0 S1 T0 T1 sd td f0 f1))
  (upper : τ (@CommRingFreydChainMapSquare R S1 (@comm_ring_freyd_chain_tail_next R n S0 S1 sd st) T1 (@comm_ring_freyd_chain_tail_next R n T0 T1 td tt) (@comm_ring_freyd_chain_tail_differential R n S0 S1 sd st) (@comm_ring_freyd_chain_tail_differential R n T0 T1 td tt) f1 f2))
  (rest : τ (@CommRingFreydChainMapTail R n S1 (@comm_ring_freyd_chain_tail_next R n S0 S1 sd st) (@comm_ring_freyd_chain_tail_differential R n S0 S1 sd st) (@comm_ring_freyd_chain_tail_rest R n S0 S1 sd st) T1 (@comm_ring_freyd_chain_tail_next R n T0 T1 td tt) (@comm_ring_freyd_chain_tail_differential R n T0 T1 td tt) (@comm_ring_freyd_chain_tail_rest R n T0 T1 td tt) f2))
  ⊢ @comm_ring_freyd_chain_map_tail_rest R n S0 S1 sd st T0 T1 td tt f1 (@comm_ring_freyd_chain_map_tail_cons R n S0 S1 sd st T0 T1 td tt f1 f2 upper rest)
  ≡ rest;

assert
  (R : τ CommRing)
  (n : τ Nat_grpd)
  (S0 S1 T0 T1 : τ (@CommRingPresentation R))
  (sd : τ (@CommRingPresentationMorphism R S1 S0))
  (td : τ (@CommRingPresentationMorphism R T1 T0))
  (st : τ (@CommRingFreydChainTail R (succ n) S0 S1 sd))
  (tt : τ (@CommRingFreydChainTail R (succ n) T0 T1 td))
  (f0 : τ (@CommRingPresentationMorphism R S0 T0))
  (f1 : τ (@CommRingPresentationMorphism R S1 T1))
  (f2 : τ (@CommRingPresentationMorphism R (@comm_ring_freyd_chain_tail_next R n S0 S1 sd st) (@comm_ring_freyd_chain_tail_next R n T0 T1 td tt)))
  (lower : τ (@CommRingFreydChainMapSquare R S0 S1 T0 T1 sd td f0 f1))
  (upper : τ (@CommRingFreydChainMapSquare R S1 (@comm_ring_freyd_chain_tail_next R n S0 S1 sd st) T1 (@comm_ring_freyd_chain_tail_next R n T0 T1 td tt) (@comm_ring_freyd_chain_tail_differential R n S0 S1 sd st) (@comm_ring_freyd_chain_tail_differential R n T0 T1 td tt) f1 f2))
  (rest : τ (@CommRingFreydChainMapTail R n S1 (@comm_ring_freyd_chain_tail_next R n S0 S1 sd st) (@comm_ring_freyd_chain_tail_differential R n S0 S1 sd st) (@comm_ring_freyd_chain_tail_rest R n S0 S1 sd st) T1 (@comm_ring_freyd_chain_tail_next R n T0 T1 td tt) (@comm_ring_freyd_chain_tail_differential R n T0 T1 td tt) (@comm_ring_freyd_chain_tail_rest R n T0 T1 td tt) f2))
  ⊢ @comm_ring_freyd_homology_chain_map_upper R
      (@comm_ring_freyd_chain_tail_next R n S0 S1 sd st) S1 S0 (@comm_ring_freyd_chain_tail_next R n T0 T1 td tt) T1 T0
      (@comm_ring_freyd_chain_tail_differential R n S0 S1 sd st) sd (@comm_ring_freyd_chain_tail_differential R n T0 T1 td tt) td f2 f1 f0
      (@comm_ring_freyd_chain_map_first_homology R n S0 S1 T0 T1 sd td st tt f0 f1 lower (@comm_ring_freyd_chain_map_tail_cons R n S0 S1 sd st T0 T1 td tt f1 f2 upper rest))
  ≡ upper;

assert
  (R : τ CommRing)
  (n : τ Nat_grpd)
  (S0 S1 T0 T1 : τ (@CommRingPresentation R))
  (sd : τ (@CommRingPresentationMorphism R S1 S0))
  (td : τ (@CommRingPresentationMorphism R T1 T0))
  (st : τ (@CommRingFreydChainTail R (succ n) S0 S1 sd))
  (tt : τ (@CommRingFreydChainTail R (succ n) T0 T1 td))
  (f0 : τ (@CommRingPresentationMorphism R S0 T0))
  (f1 : τ (@CommRingPresentationMorphism R S1 T1))
  (f2 : τ (@CommRingPresentationMorphism R (@comm_ring_freyd_chain_tail_next R n S0 S1 sd st) (@comm_ring_freyd_chain_tail_next R n T0 T1 td tt)))
  (lower : τ (@CommRingFreydChainMapSquare R S0 S1 T0 T1 sd td f0 f1))
  (upper : τ (@CommRingFreydChainMapSquare R S1 (@comm_ring_freyd_chain_tail_next R n S0 S1 sd st) T1 (@comm_ring_freyd_chain_tail_next R n T0 T1 td tt) (@comm_ring_freyd_chain_tail_differential R n S0 S1 sd st) (@comm_ring_freyd_chain_tail_differential R n T0 T1 td tt) f1 f2))
  (rest : τ (@CommRingFreydChainMapTail R n S1 (@comm_ring_freyd_chain_tail_next R n S0 S1 sd st) (@comm_ring_freyd_chain_tail_differential R n S0 S1 sd st) (@comm_ring_freyd_chain_tail_rest R n S0 S1 sd st) T1 (@comm_ring_freyd_chain_tail_next R n T0 T1 td tt) (@comm_ring_freyd_chain_tail_differential R n T0 T1 td tt) (@comm_ring_freyd_chain_tail_rest R n T0 T1 td tt) f2))
  ⊢ @comm_ring_freyd_homology_chain_map_lower R
      (@comm_ring_freyd_chain_tail_next R n S0 S1 sd st) S1 S0 (@comm_ring_freyd_chain_tail_next R n T0 T1 td tt) T1 T0
      (@comm_ring_freyd_chain_tail_differential R n S0 S1 sd st) sd (@comm_ring_freyd_chain_tail_differential R n T0 T1 td tt) td f2 f1 f0
      (@comm_ring_freyd_chain_map_first_homology R n S0 S1 T0 T1 sd td st tt f0 f1 lower (@comm_ring_freyd_chain_map_tail_cons R n S0 S1 sd st T0 T1 td tt f1 f2 upper rest))
  ≡ lower;

assert
  (R : τ CommRing)
  (S0 S1 T0 T1 : τ (@CommRingPresentation R))
  (sd : τ (@CommRingPresentationMorphism R S1 S0))
  (td : τ (@CommRingPresentationMorphism R T1 T0))
  (st : τ (@CommRingFreydChainTail R zero S0 S1 sd))
  (ttail : τ (@CommRingFreydChainTail R zero T0 T1 td))
  (f : τ (@CommRingPresentationMorphism R S1 T1))
  ⊢ @comm_ring_freyd_chain_map_tail_nil R S0 S1 sd st T0 T1 td ttail f ≡ tt;
