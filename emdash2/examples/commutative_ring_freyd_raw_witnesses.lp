/* Preserve the original raw coefficient witness, with no new proof assumption. */
require open emdash.emdash3_2_commutative_algebra_freyd_explicit_spines;

assert
  (R : τ CommRing) (p pr q qr : τ Nat_grpd)
  (P : τ (@CommRingMatrix R p pr)) (Q : τ (@CommRingMatrix R q qr))
  (F G : τ (@CommRingMatrix R q p))
  (H : τ (@CommRingMatrix R qr p))
  (law : τ (@= (@CommRingMatrix R q p)
    (@comm_ring_matrix_comp R q qr p Q H)
    (@comm_ring_matrix_sub R q p F G)))
  ⊢ @comm_ring_presentation_agreement_from_matrices R p pr q qr P Q F G H law
    : τ (@CommRingPresentationMorphismAgreement R
      (@comm_ring_presentation_intro R p pr P)
      (@comm_ring_presentation_intro R q qr Q) F G);

assert
  (R : τ CommRing) (p pr q qr : τ Nat_grpd)
  (P : τ (@CommRingMatrix R p pr)) (Q : τ (@CommRingMatrix R q qr))
  (F G : τ (@CommRingMatrix R q p))
  (H : τ (@CommRingMatrix R qr p))
  (law : τ (@= (@CommRingMatrix R q p)
    (@comm_ring_matrix_comp R q qr p Q H)
    (@comm_ring_matrix_sub R q p F G)))
  ⊢ sigma_Fst (@comm_ring_presentation_agreement_from_matrices R p pr q qr P Q F G H law) ≡ H;

assertnot
  (R : τ CommRing) (p pr q qr : τ Nat_grpd)
  (P : τ (@CommRingMatrix R p pr)) (Q : τ (@CommRingMatrix R q qr))
  (F G : τ (@CommRingMatrix R q p))
  (H other : τ (@CommRingMatrix R qr p))
  (law : τ (@= (@CommRingMatrix R q p)
    (@comm_ring_matrix_comp R q qr p Q H)
    (@comm_ring_matrix_sub R q p F G)))
  ⊢ sigma_Fst (@comm_ring_presentation_agreement_from_matrices R p pr q qr P Q F G H law) ≡ other;
