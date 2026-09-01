/* Reviewer-facing additive and bilinear matrix-law consumer. */

require open emdash.emdash3_2_commutative_algebra_matrix_additive_laws;

symbol matrix_additive_right_distrib_reviewer
  (R : τ CommRing)
  (rows middle columns : τ Nat_grpd)
  (A : τ (@CommRingMatrix R rows middle))
  (B C : τ (@CommRingMatrix R middle columns))
  : τ (@= (@CommRingMatrix R rows columns)
      (@comm_ring_matrix_comp R rows middle columns A
        (@comm_ring_matrix_add R middle columns B C))
      (@comm_ring_matrix_add R rows columns
        (@comm_ring_matrix_comp R rows middle columns A B)
        (@comm_ring_matrix_comp R rows middle columns A C)))
≔ @comm_ring_matrix_comp_add_right_path R
    rows middle columns A B C;

symbol matrix_additive_left_distrib_reviewer
  (R : τ CommRing)
  (rows middle columns : τ Nat_grpd)
  (A B : τ (@CommRingMatrix R rows middle))
  (C : τ (@CommRingMatrix R middle columns))
  : τ (@= (@CommRingMatrix R rows columns)
      (@comm_ring_matrix_comp R rows middle columns
        (@comm_ring_matrix_add R rows middle A B) C)
      (@comm_ring_matrix_add R rows columns
        (@comm_ring_matrix_comp R rows middle columns A C)
        (@comm_ring_matrix_comp R rows middle columns B C)))
≔ @comm_ring_matrix_comp_add_left_path R
    rows middle columns A B C;

symbol matrix_additive_zero_reviewer
  (R : τ CommRing)
  (rows middle columns : τ Nat_grpd)
  (A : τ (@CommRingMatrix R rows middle))
  : τ (@= (@CommRingMatrix R rows columns)
      (@comm_ring_matrix_comp R rows middle columns A
        (@comm_ring_matrix_zero R middle columns))
      (@comm_ring_matrix_zero R rows columns))
≔ @comm_ring_matrix_comp_zero_right_path R
    rows middle columns A;

assertnot
  (R : τ CommRing)
  (rows columns : τ Nat_grpd)
  (A B : τ (@CommRingMatrix R rows columns))
  ⊢ @comm_ring_matrix_add R rows columns A B
  ≡ A;
