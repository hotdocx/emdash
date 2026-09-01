/*
  Flattened direct-sum vectors and block matrices.

  Vector concatenation reuses finite-family append. Horizontal blocks append
  column families; vertical blocks append corresponding column vectors; the
  general four-block matrix and its diagonal/inclusion/projection
  specializations remain actual `CommRingMatrix` values. This module provides
  data and constructor computation only. Algebraic block paths are supplied by
  the downstream law module.
*/

require open emdash.emdash3_2_finite_family_sums;
require open emdash.emdash3_2_commutative_algebra_finite_free_category;

// Concatenate vectors `R^m × R^n -> R^(m+n)`.
symbol comm_ring_vector_append
  (R : τ CommRing)
  (m n : τ Nat_grpd)
  (u : τ (@CommRingVector R m))
  (v : τ (@CommRingVector R n))
  : τ (@CommRingVector R (@nat_add m n))
≔ @finite_family_append
    (@comm_ring_carrier R) m n u v;

// First direct-sum vector block.
symbol comm_ring_vector_take_left
  (R : τ CommRing)
  (m n : τ Nat_grpd)
  (w : τ (@CommRingVector R (@nat_add m n)))
  : τ (@CommRingVector R m)
≔ @finite_family_take_left
    (@comm_ring_carrier R) m n w;

// Second direct-sum vector block.
symbol comm_ring_vector_drop_left
  (R : τ CommRing)
  (m n : τ Nat_grpd)
  (w : τ (@CommRingVector R (@nat_add m n)))
  : τ (@CommRingVector R n)
≔ @finite_family_drop_left
    (@comm_ring_carrier R) m n w;

// Horizontal block `[A B]`: append the two column families.
symbol comm_ring_matrix_horizontal
  (R : τ CommRing)
  (rows columns_left columns_right : τ Nat_grpd)
  (A : τ (@CommRingMatrix R rows columns_left))
  (B : τ (@CommRingMatrix R rows columns_right))
  : τ (@CommRingMatrix R rows (@nat_add columns_left columns_right))
≔ @finite_family_append
    (@CommRingVector R rows)
    columns_left columns_right A B;

// Select the left columns of a horizontal-size matrix.
symbol comm_ring_matrix_take_columns
  (R : τ CommRing)
  (rows columns_left columns_right : τ Nat_grpd)
  (A : τ (@CommRingMatrix R rows
      (@nat_add columns_left columns_right)))
  : τ (@CommRingMatrix R rows columns_left)
≔ @finite_family_take_left
    (@CommRingVector R rows)
    columns_left columns_right A;

// Select the right columns of a horizontal-size matrix.
symbol comm_ring_matrix_drop_columns
  (R : τ CommRing)
  (rows columns_left columns_right : τ Nat_grpd)
  (A : τ (@CommRingMatrix R rows
      (@nat_add columns_left columns_right)))
  : τ (@CommRingMatrix R rows columns_right)
≔ @finite_family_drop_left
    (@CommRingVector R rows)
    columns_left columns_right A;

// Vertical block `[A;B]`: append corresponding column vectors.
symbol comm_ring_matrix_vertical
  (R : τ CommRing)
  (rows_top rows_bottom columns : τ Nat_grpd)
  (A : τ (@CommRingMatrix R rows_top columns))
  (B : τ (@CommRingMatrix R rows_bottom columns))
  : τ (@CommRingMatrix R (@nat_add rows_top rows_bottom) columns)
≔ (@nat_elim
    (λ columns0 : τ Nat_grpd,
      @Function_grpd
        (@CommRingMatrix R rows_top columns0)
        (@Function_grpd
          (@CommRingMatrix R rows_bottom columns0)
          (@CommRingMatrix R (@nat_add rows_top rows_bottom) columns0)))
    (λ _ : τ (@CommRingMatrix R rows_top zero),
      λ _ : τ (@CommRingMatrix R rows_bottom zero),
        @finite_family_nil
          (@CommRingVector R (@nat_add rows_top rows_bottom)))
    (λ columns0 : τ Nat_grpd,
      λ rec : τ (@Function_grpd
        (@CommRingMatrix R rows_top columns0)
        (@Function_grpd
          (@CommRingMatrix R rows_bottom columns0)
          (@CommRingMatrix R
            (@nat_add rows_top rows_bottom) columns0))),
      λ A0 : τ (@CommRingMatrix R rows_top (succ columns0)),
      λ B0 : τ (@CommRingMatrix R rows_bottom (succ columns0)),
        @finite_family_cons
          (@CommRingVector R (@nat_add rows_top rows_bottom))
          columns0
          (@comm_ring_vector_append R rows_top rows_bottom
            (@finite_family_head (@CommRingVector R rows_top) columns0 A0)
            (@finite_family_head (@CommRingVector R rows_bottom) columns0 B0))
          (rec
            (@finite_family_tail (@CommRingVector R rows_top) columns0 A0)
            (@finite_family_tail
              (@CommRingVector R rows_bottom) columns0 B0)))
    columns) A B;

// Take the top row block of every column.
symbol comm_ring_matrix_take_rows
  (R : τ CommRing)
  (rows_top rows_bottom columns : τ Nat_grpd)
  (A : τ (@CommRingMatrix R
      (@nat_add rows_top rows_bottom) columns))
  : τ (@CommRingMatrix R rows_top columns)
≔ @finite_family_map
    (@CommRingVector R (@nat_add rows_top rows_bottom))
    (@CommRingVector R rows_top)
    (λ column : τ (@CommRingVector R (@nat_add rows_top rows_bottom)),
      @comm_ring_vector_take_left R rows_top rows_bottom column)
    columns A;

// Drop the top row block of every column.
symbol comm_ring_matrix_drop_rows
  (R : τ CommRing)
  (rows_top rows_bottom columns : τ Nat_grpd)
  (A : τ (@CommRingMatrix R
      (@nat_add rows_top rows_bottom) columns))
  : τ (@CommRingMatrix R rows_bottom columns)
≔ @finite_family_map
    (@CommRingVector R (@nat_add rows_top rows_bottom))
    (@CommRingVector R rows_bottom)
    (λ column : τ (@CommRingVector R (@nat_add rows_top rows_bottom)),
      @comm_ring_vector_drop_left R rows_top rows_bottom column)
    columns A;

// General flattened four-block matrix.
symbol comm_ring_matrix_block
  (R : τ CommRing)
  (rows_top rows_bottom columns_left columns_right : τ Nat_grpd)
  (A : τ (@CommRingMatrix R rows_top columns_left))
  (B : τ (@CommRingMatrix R rows_top columns_right))
  (C : τ (@CommRingMatrix R rows_bottom columns_left))
  (D : τ (@CommRingMatrix R rows_bottom columns_right))
  : τ (@CommRingMatrix R
      (@nat_add rows_top rows_bottom)
      (@nat_add columns_left columns_right))
≔ @comm_ring_matrix_vertical
    R rows_top rows_bottom (@nat_add columns_left columns_right)
    (@comm_ring_matrix_horizontal
      R rows_top columns_left columns_right A B)
    (@comm_ring_matrix_horizontal
      R rows_bottom columns_left columns_right C D);

// Block diagonal matrix with zero off-diagonal blocks.
symbol comm_ring_matrix_block_diag
  (R : τ CommRing)
  (rows_left rows_right columns_left columns_right : τ Nat_grpd)
  (A : τ (@CommRingMatrix R rows_left columns_left))
  (D : τ (@CommRingMatrix R rows_right columns_right))
  : τ (@CommRingMatrix R
      (@nat_add rows_left rows_right)
      (@nat_add columns_left columns_right))
≔ @comm_ring_matrix_block
    R rows_left rows_right columns_left columns_right
    A
    (@comm_ring_matrix_zero R rows_left columns_right)
    (@comm_ring_matrix_zero R rows_right columns_left)
    D;

// Canonical inclusion `R^m -> R^(m+n)`.
symbol comm_ring_matrix_inl
  (R : τ CommRing)
  (m n : τ Nat_grpd)
  : τ (@CommRingMatrix R (@nat_add m n) m)
≔ @comm_ring_matrix_vertical R m n m
    (@comm_ring_finite_free_id_matrix R m)
    (@comm_ring_matrix_zero R n m);

// Canonical inclusion `R^n -> R^(m+n)`.
symbol comm_ring_matrix_inr
  (R : τ CommRing)
  (m n : τ Nat_grpd)
  : τ (@CommRingMatrix R (@nat_add m n) n)
≔ @comm_ring_matrix_vertical R m n n
    (@comm_ring_matrix_zero R m n)
    (@comm_ring_finite_free_id_matrix R n);

// Canonical projection `R^(m+n) -> R^m`.
symbol comm_ring_matrix_proj1
  (R : τ CommRing)
  (m n : τ Nat_grpd)
  : τ (@CommRingMatrix R m (@nat_add m n))
≔ @comm_ring_matrix_horizontal R m m n
    (@comm_ring_finite_free_id_matrix R m)
    (@comm_ring_matrix_zero R m n);

// Canonical projection `R^(m+n) -> R^n`.
symbol comm_ring_matrix_proj2
  (R : τ CommRing)
  (m n : τ Nat_grpd)
  : τ (@CommRingMatrix R n (@nat_add m n))
≔ @comm_ring_matrix_horizontal R n m n
    (@comm_ring_matrix_zero R n m)
    (@comm_ring_finite_free_id_matrix R n);
