/* Matrix data supplies the original triple-zero witness, before any universality. */
require open emdash.emdash3_2_commutative_algebra_freyd_explicit_spines;

symbol comm_ring_freyd_snake_zero_from_matrices
  (R : τ CommRing) (pa ra pb rb px rx pd rd : τ Nat_grpd)
  (PA : τ (@CommRingMatrix R pa ra)) (PB : τ (@CommRingMatrix R pb rb))
  (PX : τ (@CommRingMatrix R px rx)) (PD : τ (@CommRingMatrix R pd rd))
  (F : τ (@CommRingMatrix R pb pa)) (WF : τ (@CommRingMatrix R rb ra))
  (lawF : τ (@= (@CommRingMatrix R pb ra)
    (@comm_ring_matrix_comp R pb rb ra PB WF) (@comm_ring_matrix_comp R pb pa ra F PA)))
  (G : τ (@CommRingMatrix R px pb)) (WG : τ (@CommRingMatrix R rx rb))
  (lawG : τ (@= (@CommRingMatrix R px rb)
    (@comm_ring_matrix_comp R px rx rb PX WG) (@comm_ring_matrix_comp R px pb rb G PB)))
  (H : τ (@CommRingMatrix R pd px)) (WH : τ (@CommRingMatrix R rd rx))
  (lawH : τ (@= (@CommRingMatrix R pd rx)
    (@comm_ring_matrix_comp R pd rd rx PD WH) (@comm_ring_matrix_comp R pd px rx H PX)))
  (Z : τ (@CommRingMatrix R rd pa))
  (law : τ (@= (@CommRingMatrix R pd pa)
    (@comm_ring_matrix_comp R pd rd pa PD Z)
    (@comm_ring_matrix_sub R pd pa
      (@comm_ring_matrix_comp R pd px pa H (@comm_ring_matrix_comp R px pb pa G F))
      (@comm_ring_matrix_zero R pd pa))))
  : τ (@CommRingFreydChainPair R
    (@comm_ring_presentation_intro R pa ra PA)
    (@comm_ring_presentation_intro R px rx PX)
    (@comm_ring_presentation_intro R pd rd PD)
    (@comm_ring_presentation_morphism_comp R
      (@comm_ring_presentation_intro R pa ra PA)
      (@comm_ring_presentation_intro R pb rb PB)
      (@comm_ring_presentation_intro R px rx PX)
      (@comm_ring_presentation_morphism_from_matrices R pb rb px rx PB PX G WG lawG)
      (@comm_ring_presentation_morphism_from_matrices R pa ra pb rb PA PB F WF lawF))
    (@comm_ring_presentation_morphism_from_matrices R px rx pd rd PX PD H WH lawH))
≔ @comm_ring_presentation_morphism_agreement_intro R
    (@comm_ring_presentation_intro R pa ra PA) (@comm_ring_presentation_intro R pd rd PD)
    (@comm_ring_matrix_comp R pd px pa H (@comm_ring_matrix_comp R px pb pa G F))
    (@comm_ring_matrix_zero R pd pa) Z law;
