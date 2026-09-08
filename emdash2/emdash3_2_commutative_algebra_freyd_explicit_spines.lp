/*
  Explicit-data usability introductions for formal Freyd spines.

  These transparent definitions expose matrix ranks and semantic equations
  to a signature-only proof-CAS frontend. They return the existing whole
  presentation morphism and chain-pair types, delegating to their original
  constructors. They add no primitive structure, rule, or equality axiom.
*/

require open emdash.emdash3_2_commutative_algebra_freyd_bounded_complexes;

// R_Q W = F R_P constructs the original presentation morphism.
symbol comm_ring_presentation_morphism_from_matrices
  (R : τ CommRing)
  (p pr q qr : τ Nat_grpd)
  (P : τ (@CommRingMatrix R p pr))
  (Q : τ (@CommRingMatrix R q qr))
  (F : τ (@CommRingMatrix R q p))
  (W : τ (@CommRingMatrix R qr pr))
  (law : τ (@= (@CommRingMatrix R q pr)
    (@comm_ring_matrix_comp R q qr pr Q W)
    (@comm_ring_matrix_comp R q p pr F P)))
  : τ (@CommRingPresentationMorphism R
      (@comm_ring_presentation_intro R p pr P)
      (@comm_ring_presentation_intro R q qr Q))
≔ @comm_ring_presentation_morphism_intro R
    (@comm_ring_presentation_intro R p pr P)
    (@comm_ring_presentation_intro R q qr Q) F W law;

// R_0 H = G F - 0 gives the original raw chain-pair agreement.
symbol comm_ring_freyd_chain_pair_from_matrices
  (R : τ CommRing)
  (p2 r2 p1 r1 p0 r0 : τ Nat_grpd)
  (P2 : τ (@CommRingMatrix R p2 r2))
  (P1 : τ (@CommRingMatrix R p1 r1))
  (P0 : τ (@CommRingMatrix R p0 r0))
  (F : τ (@CommRingMatrix R p1 p2))
  (WF : τ (@CommRingMatrix R r1 r2))
  (lawF : τ (@= (@CommRingMatrix R p1 r2)
    (@comm_ring_matrix_comp R p1 r1 r2 P1 WF)
    (@comm_ring_matrix_comp R p1 p2 r2 F P2)))
  (G : τ (@CommRingMatrix R p0 p1))
  (WG : τ (@CommRingMatrix R r0 r1))
  (lawG : τ (@= (@CommRingMatrix R p0 r1)
    (@comm_ring_matrix_comp R p0 r0 r1 P0 WG)
    (@comm_ring_matrix_comp R p0 p1 r1 G P1)))
  (H : τ (@CommRingMatrix R r0 p2))
  (law : τ (@= (@CommRingMatrix R p0 p2)
    (@comm_ring_matrix_comp R p0 r0 p2 P0 H)
    (@comm_ring_matrix_sub R p0 p2
      (@comm_ring_matrix_comp R p0 p1 p2 G F)
      (@comm_ring_matrix_zero R p0 p2))))
  : τ (@CommRingFreydChainPair R
      (@comm_ring_presentation_intro R p2 r2 P2)
      (@comm_ring_presentation_intro R p1 r1 P1)
      (@comm_ring_presentation_intro R p0 r0 P0)
      (@comm_ring_presentation_morphism_from_matrices R
        p2 r2 p1 r1 P2 P1 F WF lawF)
      (@comm_ring_presentation_morphism_from_matrices R
        p1 r1 p0 r0 P1 P0 G WG lawG))
≔ @comm_ring_presentation_morphism_agreement_intro R
    (@comm_ring_presentation_intro R p2 r2 P2)
    (@comm_ring_presentation_intro R p0 r0 P0)
    (@comm_ring_matrix_comp R p0 p1 p2 G F)
    (@comm_ring_matrix_zero R p0 p2) H law;

// Transparent alias for the original raw agreement at literal presentation data.
symbol CommRingPresentationAgreementAtMatrices
  (R : τ CommRing) (p pr q qr : τ Nat_grpd)
  (P : τ (@CommRingMatrix R p pr)) (Q : τ (@CommRingMatrix R q qr))
  (F G : τ (@CommRingMatrix R q p))
  : Grpd
≔ @CommRingPresentationMorphismAgreement R
    (@comm_ring_presentation_intro R p pr P)
    (@comm_ring_presentation_intro R q qr Q) F G;

// R_Q H = F - G constructs the original coefficient witness and its law.
symbol comm_ring_presentation_agreement_from_matrices
  (R : τ CommRing) (p pr q qr : τ Nat_grpd)
  (P : τ (@CommRingMatrix R p pr)) (Q : τ (@CommRingMatrix R q qr))
  (F G : τ (@CommRingMatrix R q p))
  (H : τ (@CommRingMatrix R qr p))
  (law : τ (@= (@CommRingMatrix R q p)
    (@comm_ring_matrix_comp R q qr p Q H)
    (@comm_ring_matrix_sub R q p F G)))
  : τ (@CommRingPresentationAgreementAtMatrices R p pr q qr P Q F G)
≔ @comm_ring_presentation_morphism_agreement_intro R
    (@comm_ring_presentation_intro R p pr P)
    (@comm_ring_presentation_intro R q qr Q) F G H law;
