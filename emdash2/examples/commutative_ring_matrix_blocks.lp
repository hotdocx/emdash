/* Reviewer-facing flattened vector and matrix blocks. */

require open emdash.emdash3_2_commutative_algebra_matrix_block_laws;

assert (R : τ CommRing)
  (m n : τ Nat_grpd)
  (u : τ (@CommRingVector R m))
  (v : τ (@CommRingVector R n)) ⊢
  @comm_ring_vector_append R m n u v
  : τ (@CommRingVector R (@nat_add m n));

assert (R : τ CommRing)
  (rows columns_left columns_right : τ Nat_grpd)
  (A : τ (@CommRingMatrix R rows columns_left))
  (B : τ (@CommRingMatrix R rows columns_right)) ⊢
  @comm_ring_matrix_horizontal R rows columns_left columns_right A B
  : τ (@CommRingMatrix R rows (@nat_add columns_left columns_right));

assert (R : τ CommRing)
  (rows_top rows_bottom columns : τ Nat_grpd)
  (A : τ (@CommRingMatrix R rows_top columns))
  (B : τ (@CommRingMatrix R rows_bottom columns)) ⊢
  @comm_ring_matrix_vertical R rows_top rows_bottom columns A B
  : τ (@CommRingMatrix R (@nat_add rows_top rows_bottom) columns);

assert (R : τ CommRing)
  (r0 r1 c0 c1 : τ Nat_grpd)
  (A : τ (@CommRingMatrix R r0 c0))
  (D : τ (@CommRingMatrix R r1 c1)) ⊢
  @comm_ring_matrix_block_diag R r0 r1 c0 c1 A D
  : τ (@CommRingMatrix R (@nat_add r0 r1) (@nat_add c0 c1));

assert (R : τ CommRing)
  (m n : τ Nat_grpd) ⊢
  @comm_ring_matrix_proj1 R m n
  : τ (@CommRingMatrix R m (@nat_add m n));

assertnot (R : τ CommRing)
  (m : τ Nat_grpd) ⊢
  @comm_ring_matrix_inl R m m
  ≡ @comm_ring_matrix_inr R m m;

assert (R : τ CommRing)
  (m n columns : τ Nat_grpd)
  (F : τ (@CommRingMatrix R m columns))
  (G : τ (@CommRingMatrix R n columns)) ⊢
  @comm_ring_matrix_proj1_vertical_path R m n columns F G
  : τ (@= (@CommRingMatrix R m columns)
      (@comm_ring_matrix_comp R m (@nat_add m n) columns
        (@comm_ring_matrix_proj1 R m n)
        (@comm_ring_matrix_vertical R m n columns F G))
      F);

assert (R : τ CommRing)
  (m n columns : τ Nat_grpd)
  (H : τ (@CommRingMatrix R (@nat_add m n) columns)) ⊢
  @comm_ring_matrix_vertical_proj_eta_path R m n columns H
  : τ (@= (@CommRingMatrix R (@nat_add m n) columns)
      (@comm_ring_matrix_vertical R m n columns
        (@comm_ring_matrix_comp R m (@nat_add m n) columns
          (@comm_ring_matrix_proj1 R m n) H)
        (@comm_ring_matrix_comp R n (@nat_add m n) columns
          (@comm_ring_matrix_proj2 R m n) H))
      H);

assert (R : τ CommRing)
  (r0 r1 m0 m1 c0 c1 : τ Nat_grpd)
  (A : τ (@CommRingMatrix R r0 m0))
  (D : τ (@CommRingMatrix R r1 m1))
  (B : τ (@CommRingMatrix R m0 c0))
  (E : τ (@CommRingMatrix R m1 c1)) ⊢
  @comm_ring_matrix_block_diag_comp_path
    R r0 r1 m0 m1 c0 c1 A D B E
  : τ (@= (@CommRingMatrix R (@nat_add r0 r1) (@nat_add c0 c1))
      (@comm_ring_matrix_comp R (@nat_add r0 r1) (@nat_add m0 m1)
        (@nat_add c0 c1)
        (@comm_ring_matrix_block_diag R r0 r1 m0 m1 A D)
        (@comm_ring_matrix_block_diag R m0 m1 c0 c1 B E))
      (@comm_ring_matrix_block_diag R r0 r1 c0 c1
        (@comm_ring_matrix_comp R r0 m0 c0 A B)
        (@comm_ring_matrix_comp R r1 m1 c1 D E)));
