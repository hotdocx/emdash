/*
  Explicit-data introduction for the existing witnessed Freyd epimorphism.

  The block identity Q U + F V = id constructs the zero agreement for the
  canonical cokernel projection. The witness is the retained vertical block
  [U;V]. The input morphism is the original explicit-spine constructor.
  This supplies boundary epicity, not cycle universality or chain exactness.
  No rewrite, unification rule, or equality axiom is introduced.
*/

require open emdash.emdash3_2_commutative_algebra_freyd_explicit_spines;

// Q U + F V = id gives the original cokernel-projection zero agreement.
symbol comm_ring_freyd_epimorphism_from_matrices
  (R : τ CommRing)
  (p pr q qr : τ Nat_grpd)
  (P : τ (@CommRingMatrix R p pr))
  (Q : τ (@CommRingMatrix R q qr))
  (F : τ (@CommRingMatrix R q p))
  (W : τ (@CommRingMatrix R qr pr))
  (lawF : τ (@= (@CommRingMatrix R q pr)
    (@comm_ring_matrix_comp R q qr pr Q W)
    (@comm_ring_matrix_comp R q p pr F P)))
  (U : τ (@CommRingMatrix R qr q))
  (V : τ (@CommRingMatrix R p q))
  (lawE : τ (@= (@CommRingMatrix R q q)
    (@comm_ring_matrix_add R q q
      (@comm_ring_matrix_comp R q qr q Q U)
      (@comm_ring_matrix_comp R q p q F V))
    (@comm_ring_finite_free_id_matrix R q)))
  : τ (@CommRingFreydEpimorphismWitness R
      (@comm_ring_presentation_intro R p pr P)
      (@comm_ring_presentation_intro R q qr Q)
      (@comm_ring_presentation_morphism_from_matrices R
        p pr q qr P Q F W lawF))
≔ @comm_ring_presentation_morphism_agreement_intro R
    (@comm_ring_presentation_intro R q qr Q)
    (@comm_ring_freyd_cokernel_presentation R
      (@comm_ring_presentation_intro R p pr P)
      (@comm_ring_presentation_intro R q qr Q)
      (@comm_ring_presentation_morphism_from_matrices R
        p pr q qr P Q F W lawF))
    (@comm_ring_finite_free_id_matrix R q)
    (@comm_ring_matrix_zero R q q)
    (@comm_ring_matrix_vertical R qr p q U V)
    (@eq_trans _ _
      (@comm_ring_matrix_add R q q
        (@comm_ring_matrix_comp R q qr q Q U)
        (@comm_ring_matrix_comp R q p q F V))
      _
      (@comm_ring_matrix_horizontal_vertical_comp_path R q qr p q
        Q F U V)
      (@eq_trans _ _
        (@comm_ring_finite_free_id_matrix R q)
        _ lawE
        (@eq_sym _ _ _
          (@comm_ring_freyd_cokernel_sub_zero_path R q q
            (@comm_ring_finite_free_id_matrix R q)))));
