/* Existing whole constructors and projection computation from explicit data. */

require open emdash.emdash3_2_commutative_algebra_freyd_explicit_spines;

symbol R : τ CommRing;
symbol p2 : τ Nat_grpd;
symbol r2 : τ Nat_grpd;
symbol p1 : τ Nat_grpd;
symbol r1 : τ Nat_grpd;
symbol p0 : τ Nat_grpd;
symbol r0 : τ Nat_grpd;
symbol P2 : τ (@CommRingMatrix R p2 r2);
symbol P1 : τ (@CommRingMatrix R p1 r1);
symbol P0 : τ (@CommRingMatrix R p0 r0);
symbol F : τ (@CommRingMatrix R p1 p2);
symbol WF : τ (@CommRingMatrix R r1 r2);
symbol lawF : τ (@= (@CommRingMatrix R p1 r2)
  (@comm_ring_matrix_comp R p1 r1 r2 P1 WF)
  (@comm_ring_matrix_comp R p1 p2 r2 F P2));
symbol G : τ (@CommRingMatrix R p0 p1);
symbol WG : τ (@CommRingMatrix R r0 r1);
symbol lawG : τ (@= (@CommRingMatrix R p0 r1)
  (@comm_ring_matrix_comp R p0 r0 r1 P0 WG)
  (@comm_ring_matrix_comp R p0 p1 r1 G P1));
symbol H : τ (@CommRingMatrix R r0 p2);
symbol law : τ (@= (@CommRingMatrix R p0 p2)
  (@comm_ring_matrix_comp R p0 r0 p2 P0 H)
  (@comm_ring_matrix_sub R p0 p2
    (@comm_ring_matrix_comp R p0 p1 p2 G F)
    (@comm_ring_matrix_zero R p0 p2)));

symbol S2 : τ (@CommRingPresentation R) ≔ @comm_ring_presentation_intro R p2 r2 P2;
symbol S1 : τ (@CommRingPresentation R) ≔ @comm_ring_presentation_intro R p1 r1 P1;
symbol S0 : τ (@CommRingPresentation R) ≔ @comm_ring_presentation_intro R p0 r0 P0;
symbol f : τ (@CommRingPresentationMorphism R S2 S1)
≔ @comm_ring_presentation_morphism_from_matrices R
  p2 r2 p1 r1 P2 P1 F WF lawF;
symbol g : τ (@CommRingPresentationMorphism R S1 S0)
≔ @comm_ring_presentation_morphism_from_matrices R
  p1 r1 p0 r0 P1 P0 G WG lawG;
symbol pair : τ (@CommRingFreydChainPair R S2 S1 S0 f g)
≔ @comm_ring_freyd_chain_pair_from_matrices R
  p2 r2 p1 r1 p0 r0 P2 P1 P0 F WF lawF G WG lawG H law;
symbol rest : τ (@CommRingFreydChainTail R zero S1 S2 f)
≔ @comm_ring_freyd_chain_tail_nil R S1 S2 f;
symbol tail : τ (@CommRingFreydChainTail R (succ zero) S0 S1 g)
≔ @comm_ring_freyd_chain_tail_cons R zero S0 S1 g S2 f pair rest;
symbol spine : τ (@CommRingFreydBoundedComplex R (succ (succ zero)))
≔ @comm_ring_freyd_bounded_complex_succ R (succ zero) S0 S1 g tail;

assert ⊢ f : τ (@CommRingPresentationMorphism R S2 S1);
assert ⊢ g : τ (@CommRingPresentationMorphism R S1 S0);
assert ⊢ pair : τ (@CommRingFreydChainPair R S2 S1 S0 f g);
assert ⊢ spine : τ (@CommRingFreydBoundedComplex R (succ (succ zero)));
assert ⊢ @comm_ring_presentation_morphism_map R S2 S1 f ≡ F;
assert ⊢ @comm_ring_presentation_morphism_witness R S2 S1 f ≡ WF;
assert ⊢ @comm_ring_presentation_morphism_law R S2 S1 f ≡ lawF;
assert ⊢ @comm_ring_presentation_morphism_map R S1 S0 g ≡ G;
assert ⊢ @comm_ring_freyd_bounded_complex_P0 R (succ zero) spine ≡ S0;
assert ⊢ @comm_ring_freyd_bounded_complex_P1 R (succ zero) spine ≡ S1;
assert ⊢ @comm_ring_freyd_bounded_complex_d1 R (succ zero) spine ≡ g;
assert ⊢ @comm_ring_freyd_bounded_complex_tail R (succ zero) spine ≡ tail;
assert ⊢ @comm_ring_freyd_chain_tail_next R zero S0 S1 g tail ≡ S2;
assert ⊢ @comm_ring_freyd_chain_tail_differential R zero S0 S1 g tail ≡ f;
assert ⊢ @comm_ring_freyd_chain_tail_law R zero S0 S1 g tail ≡ pair;
assert ⊢ @comm_ring_freyd_chain_tail_rest R zero S0 S1 g tail ≡ rest;

// Wrong arrow endpoints and an unrelated matrix equation do not typecheck.
assertnot ⊢ f : τ (@CommRingPresentationMorphism R S1 S0);
assertnot ⊢ @comm_ring_freyd_chain_pair_from_matrices R
  p2 r2 p1 r1 p0 r0 P2 P1 P0 F WF lawF G WG lawG H lawF
  : τ (@CommRingFreydChainPair R S2 S1 S0 f g);
