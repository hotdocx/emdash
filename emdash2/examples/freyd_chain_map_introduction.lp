/* Original semantic matrix products introduce the existing chain-map owner. */
require open emdash.emdash3_2_commutative_algebra_freyd_chain_map_introduction;

symbol R : τ CommRing;
symbol n0 : τ Nat_grpd;
symbol r0 : τ Nat_grpd;
symbol n1 : τ Nat_grpd;
symbol r1 : τ Nat_grpd;
symbol n2 : τ Nat_grpd;
symbol r2 : τ Nat_grpd;
symbol n3 : τ Nat_grpd;
symbol r3 : τ Nat_grpd;
symbol n4 : τ Nat_grpd;
symbol r4 : τ Nat_grpd;
symbol n5 : τ Nat_grpd;
symbol r5 : τ Nat_grpd;
symbol P0 : τ (@CommRingMatrix R n0 r0);
symbol P1 : τ (@CommRingMatrix R n1 r1);
symbol P2 : τ (@CommRingMatrix R n2 r2);
symbol P3 : τ (@CommRingMatrix R n3 r3);
symbol P4 : τ (@CommRingMatrix R n4 r4);
symbol P5 : τ (@CommRingMatrix R n5 r5);
symbol E0 : τ (@CommRingMatrix R n1 n0);
symbol WE0 : τ (@CommRingMatrix R r1 r0);
symbol lawE0 : τ (@= (@CommRingMatrix R n1 r0)
    (@comm_ring_matrix_comp R n1 r1 r0 P1 WE0)
    (@comm_ring_matrix_comp R n1 n0 r0 E0 P0));
symbol D0 : τ (@CommRingMatrix R n2 n1);
symbol WD0 : τ (@CommRingMatrix R r2 r1);
symbol lawD0 : τ (@= (@CommRingMatrix R n2 r1)
    (@comm_ring_matrix_comp R n2 r2 r1 P2 WD0)
    (@comm_ring_matrix_comp R n2 n1 r1 D0 P1));
symbol E1 : τ (@CommRingMatrix R n4 n3);
symbol WE1 : τ (@CommRingMatrix R r4 r3);
symbol lawE1 : τ (@= (@CommRingMatrix R n4 r3)
    (@comm_ring_matrix_comp R n4 r4 r3 P4 WE1)
    (@comm_ring_matrix_comp R n4 n3 r3 E1 P3));
symbol D1 : τ (@CommRingMatrix R n5 n4);
symbol WD1 : τ (@CommRingMatrix R r5 r4);
symbol lawD1 : τ (@= (@CommRingMatrix R n5 r4)
    (@comm_ring_matrix_comp R n5 r5 r4 P5 WD1)
    (@comm_ring_matrix_comp R n5 n4 r4 D1 P4));
symbol A2 : τ (@CommRingMatrix R n3 n0);
symbol WA2 : τ (@CommRingMatrix R r3 r0);
symbol lawA2 : τ (@= (@CommRingMatrix R n3 r0)
    (@comm_ring_matrix_comp R n3 r3 r0 P3 WA2)
    (@comm_ring_matrix_comp R n3 n0 r0 A2 P0));
symbol A1 : τ (@CommRingMatrix R n4 n1);
symbol WA1 : τ (@CommRingMatrix R r4 r1);
symbol lawA1 : τ (@= (@CommRingMatrix R n4 r1)
    (@comm_ring_matrix_comp R n4 r4 r1 P4 WA1)
    (@comm_ring_matrix_comp R n4 n1 r1 A1 P1));
symbol A0 : τ (@CommRingMatrix R n5 n2);
symbol WA0 : τ (@CommRingMatrix R r5 r2);
symbol lawA0 : τ (@= (@CommRingMatrix R n5 r2)
    (@comm_ring_matrix_comp R n5 r5 r2 P5 WA0)
    (@comm_ring_matrix_comp R n5 n2 r2 A0 P2));
symbol upper : τ (@CommRingMatrix R r4 n0);
symbol upperLaw : τ (@= (@CommRingMatrix R n4 n0)
    (@comm_ring_matrix_comp R n4 r4 n0 P4 upper)
    (@comm_ring_matrix_sub R n4 n0 (@comm_ring_matrix_comp R n4 n3 n0 E1 A2) (@comm_ring_matrix_comp R n4 n1 n0 A1 E0)));
symbol lower : τ (@CommRingMatrix R r5 n1);
symbol lowerLaw : τ (@= (@CommRingMatrix R n5 n1)
    (@comm_ring_matrix_comp R n5 r5 n1 P5 lower)
    (@comm_ring_matrix_sub R n5 n1 (@comm_ring_matrix_comp R n5 n4 n1 D1 A1) (@comm_ring_matrix_comp R n5 n2 n1 A0 D0)));

symbol chain : τ (@CommRingFreydHomologyChainMap R
      (@comm_ring_presentation_intro R n0 r0 P0)
      (@comm_ring_presentation_intro R n1 r1 P1)
      (@comm_ring_presentation_intro R n2 r2 P2)
      (@comm_ring_presentation_intro R n3 r3 P3)
      (@comm_ring_presentation_intro R n4 r4 P4)
      (@comm_ring_presentation_intro R n5 r5 P5)
      (@comm_ring_presentation_morphism_from_matrices R n0 r0 n1 r1 P0 P1 E0 WE0 lawE0)
      (@comm_ring_presentation_morphism_from_matrices R n1 r1 n2 r2 P1 P2 D0 WD0 lawD0)
      (@comm_ring_presentation_morphism_from_matrices R n3 r3 n4 r4 P3 P4 E1 WE1 lawE1)
      (@comm_ring_presentation_morphism_from_matrices R n4 r4 n5 r5 P4 P5 D1 WD1 lawD1)
      (@comm_ring_presentation_morphism_from_matrices R n0 r0 n3 r3 P0 P3 A2 WA2 lawA2)
      (@comm_ring_presentation_morphism_from_matrices R n1 r1 n4 r4 P1 P4 A1 WA1 lawA1)
      (@comm_ring_presentation_morphism_from_matrices R n2 r2 n5 r5 P2 P5 A0 WA0 lawA0))
≔ @comm_ring_freyd_chain_map_from_matrices R n0 r0 n1 r1 n2 r2 n3 r3 n4 r4 n5 r5 P0 P1 P2 P3 P4 P5 E0 WE0 lawE0 D0 WD0 lawD0 E1 WE1 lawE1 D1 WD1 lawD1 A2 WA2 lawA2 A1 WA1 lawA1 A0 WA0 lawA0 upper upperLaw lower lowerLaw;

// Both original coefficient witnesses and their semantic laws are retained.
assert ⊢ sigma_Fst (sigma_Fst chain) ≡ upper;
assert ⊢ sigma_Snd (sigma_Fst chain) ≡ upperLaw;
assert ⊢ sigma_Fst (sigma_Snd chain) ≡ lower;
assert ⊢ sigma_Snd (sigma_Snd chain) ≡ lowerLaw;
symbol otherUpper : τ (@CommRingMatrix R r4 n0);
assertnot ⊢ sigma_Fst (sigma_Fst chain) ≡ otherUpper;
