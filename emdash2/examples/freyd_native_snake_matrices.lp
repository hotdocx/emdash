/* The matrix introduction retains both its coefficient witness and equation. */
require open emdash.emdash3_2_commutative_algebra_freyd_native_snake_matrices;

assert (R : τ CommRing) (pa ra pb rb px rx pd rd : τ Nat_grpd)
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
      (@comm_ring_matrix_zero R pd pa)))) ⊢
  sigma_Fst (@comm_ring_freyd_snake_zero_from_matrices R pa ra pb rb px rx pd rd PA PB PX PD F WF lawF G WG lawG H WH lawH Z law) ≡ Z;

assert (R : τ CommRing) (pa ra pb rb px rx pd rd : τ Nat_grpd)
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
      (@comm_ring_matrix_zero R pd pa)))) ⊢
  sigma_Snd (@comm_ring_freyd_snake_zero_from_matrices R pa ra pb rb px rx pd rd PA PB PX PD F WF lawF G WG lawG H WH lawH Z law) ≡ law;
