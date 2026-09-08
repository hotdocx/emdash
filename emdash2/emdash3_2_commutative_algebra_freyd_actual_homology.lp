/*
  Literal-data homology and exactness at the actual selected kernel choices.
  The given boundary and raw relation witness are retained verbatim.
  All constructions delegate to the selected homology/provider owners.
*/
require open emdash.emdash3_2_commutative_algebra_freyd_kernel_choice_providers;
require open emdash.emdash3_2_commutative_algebra_freyd_selected_homology;
require open emdash.emdash3_2_commutative_algebra_freyd_explicit_epimorphisms;

// R_1 H = p1 B - F supplies the existing raw boundary reconstruction.
symbol comm_ring_freyd_homology_from_matrix_providers
  (R : τ CommRing) (n2 r2 n1 r1 n0 r0 : τ Nat_grpd)
  (P2 : τ (@CommRingMatrix R n2 r2))
  (P1 : τ (@CommRingMatrix R n1 r1))
  (P0 : τ (@CommRingMatrix R n0 r0))
  (F : τ (@CommRingMatrix R n1 n2)) (WF : τ (@CommRingMatrix R r1 r2))
  (lawF : τ (@= (@CommRingMatrix R n1 r2)
    (@comm_ring_matrix_comp R n1 r1 r2 P1 WF)
    (@comm_ring_matrix_comp R n1 n2 r2 F P2)))
  (G : τ (@CommRingMatrix R n0 n1)) (WG : τ (@CommRingMatrix R r0 r1))
  (lawG : τ (@= (@CommRingMatrix R n0 r1)
    (@comm_ring_matrix_comp R n0 r0 r1 P0 WG)
    (@comm_ring_matrix_comp R n0 n1 r1 G P1)))
  (chain : τ (@CommRingFreydChainPair R (@comm_ring_presentation_intro R n2 r2 P2) (@comm_ring_presentation_intro R n1 r1 P1) (@comm_ring_presentation_intro R n0 r0 P0) (@comm_ring_presentation_morphism_from_matrices R n2 r2 n1 r1 P2 P1 F WF lawF) (@comm_ring_presentation_morphism_from_matrices R n1 r1 n0 r0 P1 P0 G WG lawG)))
  (k1 : τ Nat_grpd)
  (p1 : τ (@CommRingMatrix R n1 k1)) (q1 : τ (@CommRingMatrix R r0 k1))
  (compatible1 : τ (@= (@CommRingMatrix R n0 k1)
    (@comm_ring_matrix_comp R n0 n1 k1 G p1)
    (@comm_ring_matrix_comp R n0 r0 k1 P0 q1)))
  (provider1 : τ (@CommRingFiniteFreeWeakPullbackMatrixProvider
    R n1 n0 r0 k1 G P0 p1 q1 compatible1))
  (k2 : τ Nat_grpd)
  (p2 : τ (@CommRingMatrix R k1 k2)) (q2 : τ (@CommRingMatrix R r1 k2))
  (compatible2 : τ (@= (@CommRingMatrix R n1 k2)
    (@comm_ring_matrix_comp R n1 k1 k2 p1 p2)
    (@comm_ring_matrix_comp R n1 r1 k2 P1 q2)))
  (provider2 : τ (@CommRingFiniteFreeWeakPullbackMatrixProvider
    R k1 n1 r1 k2 p1 P1 p2 q2 compatible2))
  (B : τ (@CommRingMatrix R k1 n2)) (WB : τ (@CommRingMatrix R k2 r2))
  (lawB : τ (@= (@CommRingMatrix R k1 r2)
    (@comm_ring_matrix_comp R k1 k2 r2 p2 WB)
    (@comm_ring_matrix_comp R k1 n2 r2 B P2)))
  (H : τ (@CommRingMatrix R r1 n2))
  (lawH : τ (@= (@CommRingMatrix R n1 n2)
    (@comm_ring_matrix_comp R n1 r1 n2 P1 H)
    (@comm_ring_matrix_sub R n1 n2
      (@comm_ring_matrix_comp R n1 k1 n2 p1 B) F)))
  : τ (@CommRingFreydSelectedHomologyAt R (@comm_ring_presentation_intro R n2 r2 P2) (@comm_ring_presentation_intro R n1 r1 P1) (@comm_ring_presentation_intro R n0 r0 P0) (@comm_ring_presentation_morphism_from_matrices R n2 r2 n1 r1 P2 P1 F WF lawF) (@comm_ring_presentation_morphism_from_matrices R n1 r1 n0 r0 P1 P0 G WG lawG) (@comm_ring_freyd_kernel_choices_from_matrix_providers R n1 r1 n0 r0 P1 P0 G WG lawG k1 p1 q1 compatible1 provider1 k2 p2 q2 compatible2 provider2) chain)
≔ @comm_ring_freyd_selected_homology_from_boundary R
    (@comm_ring_presentation_intro R n2 r2 P2) (@comm_ring_presentation_intro R n1 r1 P1) (@comm_ring_presentation_intro R n0 r0 P0) (@comm_ring_presentation_morphism_from_matrices R n2 r2 n1 r1 P2 P1 F WF lawF) (@comm_ring_presentation_morphism_from_matrices R n1 r1 n0 r0 P1 P0 G WG lawG) (@comm_ring_freyd_kernel_choices_from_matrix_providers R n1 r1 n0 r0 P1 P0 G WG lawG k1 p1 q1 compatible1 provider1 k2 p2 q2 compatible2 provider2) chain (@comm_ring_presentation_morphism_from_matrices R n2 r2 k1 k2 P2 p2 B WB lawB)
    (@comm_ring_presentation_morphism_agreement_intro R (@comm_ring_presentation_intro R n2 r2 P2) (@comm_ring_presentation_intro R n1 r1 P1)
      (@comm_ring_matrix_comp R n1 k1 n2 p1 B) F H lawH);

// The already constructed epimorphism witness is exactness at that same boundary.
symbol comm_ring_freyd_exactness_from_matrix_providers
  (R : τ CommRing) (n2 r2 n1 r1 n0 r0 : τ Nat_grpd)
  (P2 : τ (@CommRingMatrix R n2 r2))
  (P1 : τ (@CommRingMatrix R n1 r1))
  (P0 : τ (@CommRingMatrix R n0 r0))
  (F : τ (@CommRingMatrix R n1 n2)) (WF : τ (@CommRingMatrix R r1 r2))
  (lawF : τ (@= (@CommRingMatrix R n1 r2)
    (@comm_ring_matrix_comp R n1 r1 r2 P1 WF)
    (@comm_ring_matrix_comp R n1 n2 r2 F P2)))
  (G : τ (@CommRingMatrix R n0 n1)) (WG : τ (@CommRingMatrix R r0 r1))
  (lawG : τ (@= (@CommRingMatrix R n0 r1)
    (@comm_ring_matrix_comp R n0 r0 r1 P0 WG)
    (@comm_ring_matrix_comp R n0 n1 r1 G P1)))
  (chain : τ (@CommRingFreydChainPair R (@comm_ring_presentation_intro R n2 r2 P2) (@comm_ring_presentation_intro R n1 r1 P1) (@comm_ring_presentation_intro R n0 r0 P0) (@comm_ring_presentation_morphism_from_matrices R n2 r2 n1 r1 P2 P1 F WF lawF) (@comm_ring_presentation_morphism_from_matrices R n1 r1 n0 r0 P1 P0 G WG lawG)))
  (k1 : τ Nat_grpd)
  (p1 : τ (@CommRingMatrix R n1 k1)) (q1 : τ (@CommRingMatrix R r0 k1))
  (compatible1 : τ (@= (@CommRingMatrix R n0 k1)
    (@comm_ring_matrix_comp R n0 n1 k1 G p1)
    (@comm_ring_matrix_comp R n0 r0 k1 P0 q1)))
  (provider1 : τ (@CommRingFiniteFreeWeakPullbackMatrixProvider
    R n1 n0 r0 k1 G P0 p1 q1 compatible1))
  (k2 : τ Nat_grpd)
  (p2 : τ (@CommRingMatrix R k1 k2)) (q2 : τ (@CommRingMatrix R r1 k2))
  (compatible2 : τ (@= (@CommRingMatrix R n1 k2)
    (@comm_ring_matrix_comp R n1 k1 k2 p1 p2)
    (@comm_ring_matrix_comp R n1 r1 k2 P1 q2)))
  (provider2 : τ (@CommRingFiniteFreeWeakPullbackMatrixProvider
    R k1 n1 r1 k2 p1 P1 p2 q2 compatible2))
  (B : τ (@CommRingMatrix R k1 n2)) (WB : τ (@CommRingMatrix R k2 r2))
  (lawB : τ (@= (@CommRingMatrix R k1 r2)
    (@comm_ring_matrix_comp R k1 k2 r2 p2 WB)
    (@comm_ring_matrix_comp R k1 n2 r2 B P2)))
  (H : τ (@CommRingMatrix R r1 n2))
  (lawH : τ (@= (@CommRingMatrix R n1 n2)
    (@comm_ring_matrix_comp R n1 r1 n2 P1 H)
    (@comm_ring_matrix_sub R n1 n2
      (@comm_ring_matrix_comp R n1 k1 n2 p1 B) F)))
  (epic : τ (@CommRingFreydEpimorphismWitness R (@comm_ring_presentation_intro R n2 r2 P2) (@comm_ring_presentation_intro R k1 k2 p2) (@comm_ring_presentation_morphism_from_matrices R n2 r2 k1 k2 P2 p2 B WB lawB)))
  : τ (@CommRingFreydSelectedExactnessAt R (@comm_ring_presentation_intro R n2 r2 P2) (@comm_ring_presentation_intro R n1 r1 P1) (@comm_ring_presentation_intro R n0 r0 P0) (@comm_ring_presentation_morphism_from_matrices R n2 r2 n1 r1 P2 P1 F WF lawF) (@comm_ring_presentation_morphism_from_matrices R n1 r1 n0 r0 P1 P0 G WG lawG) (@comm_ring_freyd_kernel_choices_from_matrix_providers R n1 r1 n0 r0 P1 P0 G WG lawG k1 p1 q1 compatible1 provider1 k2 p2 q2 compatible2 provider2) chain (@comm_ring_freyd_homology_from_matrix_providers R n2 r2 n1 r1 n0 r0 P2 P1 P0 F WF lawF G WG lawG chain k1 p1 q1 compatible1 provider1 k2 p2 q2 compatible2 provider2 B WB lawB H lawH))
≔ epic;
