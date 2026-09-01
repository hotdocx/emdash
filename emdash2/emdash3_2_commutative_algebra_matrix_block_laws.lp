/*
  Algebraic laws for flattened direct-sum vectors and block matrices.

  Paths are constructed by Nat recursion over the existing column-family
  representation and reuse the established vector/matrix additive and
  categorical identity laws. The module introduces no runtime or unification
  rule.
*/

require open emdash.emdash3_2_commutative_algebra_matrix_blocks;
require open emdash.emdash3_2_commutative_algebra_matrix_additive_laws;

// Congruence of vector concatenation in both inputs.
symbol comm_ring_vector_append_congr_path
  (R : τ CommRing)
  (m n : τ Nat_grpd)
  (u u' : τ (@CommRingVector R m))
  (v v' : τ (@CommRingVector R n))
  (p : τ (@= (@CommRingVector R m) u u'))
  (q : τ (@= (@CommRingVector R n) v v'))
  : τ (@= (@CommRingVector R (@nat_add m n))
      (@comm_ring_vector_append R m n u v)
      (@comm_ring_vector_append R m n u' v'))
≔ @eq_trans
    (@CommRingVector R (@nat_add m n))
    (@comm_ring_vector_append R m n u v)
    (@comm_ring_vector_append R m n u' v)
    (@comm_ring_vector_append R m n u' v')
    (@eq_ap
      (@CommRingVector R m)
      (@CommRingVector R (@nat_add m n))
      (λ z : τ (@CommRingVector R m),
        @comm_ring_vector_append R m n z v)
      u u' p)
    (@eq_ap
      (@CommRingVector R n)
      (@CommRingVector R (@nat_add m n))
      (λ z : τ (@CommRingVector R n),
        @comm_ring_vector_append R m n u' z)
      v v' q);

// The two zero blocks concatenate to the zero vector.
symbol comm_ring_vector_append_zero_path
  (R : τ CommRing)
  (m n : τ Nat_grpd)
  : τ (@= (@CommRingVector R (@nat_add m n))
      (@comm_ring_vector_append R m n
        (@comm_ring_vector_zero R m)
        (@comm_ring_vector_zero R n))
      (@comm_ring_vector_zero R (@nat_add m n)))
≔ @nat_elim
    (λ m0 : τ Nat_grpd,
      @= (@CommRingVector R (@nat_add m0 n))
        (@comm_ring_vector_append R m0 n
          (@comm_ring_vector_zero R m0)
          (@comm_ring_vector_zero R n))
        (@comm_ring_vector_zero R (@nat_add m0 n)))
    (@eq_refl
      (@CommRingVector R n)
      (@comm_ring_vector_zero R n))
    (λ m0 : τ Nat_grpd, λ ih : τ _,
      @finite_family_succ_path
        (@comm_ring_carrier R) (@nat_add m0 n)
        (@comm_ring_vector_append R (succ m0) n
          (@comm_ring_vector_zero R (succ m0))
          (@comm_ring_vector_zero R n))
        (@comm_ring_vector_zero R (@nat_add (succ m0) n))
        (@eq_refl
          (@comm_ring_carrier R)
          (@comm_ring_zero R))
        ih)
    m;

// Concatenation preserves componentwise vector addition.
symbol comm_ring_vector_append_add_path
  (R : τ CommRing)
  (m n : τ Nat_grpd)
  (u u' : τ (@CommRingVector R m))
  (v v' : τ (@CommRingVector R n))
  : τ (@= (@CommRingVector R (@nat_add m n))
      (@comm_ring_vector_append R m n
        (@comm_ring_vector_add R m u u')
        (@comm_ring_vector_add R n v v'))
      (@comm_ring_vector_add R (@nat_add m n)
        (@comm_ring_vector_append R m n u v)
        (@comm_ring_vector_append R m n u' v')))
≔ (@nat_elim
    (λ m0 : τ Nat_grpd,
      @Pi_grpd (@CommRingVector R m0) (λ u0 : τ _,
        @Pi_grpd (@CommRingVector R m0) (λ u0' : τ _,
          @Pi_grpd (@CommRingVector R n) (λ v0 : τ _,
            @Pi_grpd (@CommRingVector R n) (λ v0' : τ _,
              @= (@CommRingVector R (@nat_add m0 n))
                (@comm_ring_vector_append R m0 n
                  (@comm_ring_vector_add R m0 u0 u0')
                  (@comm_ring_vector_add R n v0 v0'))
                (@comm_ring_vector_add R (@nat_add m0 n)
                  (@comm_ring_vector_append R m0 n u0 v0)
                  (@comm_ring_vector_append R m0 n u0' v0')))))))
    (λ _ : τ _, λ _ : τ _, λ v0 : τ _, λ v0' : τ _,
      @eq_refl
        (@CommRingVector R n)
        (@comm_ring_vector_add R n v0 v0'))
    (λ m0 : τ Nat_grpd, λ ih : τ _,
      λ u0 : τ _, λ u0' : τ _, λ v0 : τ _, λ v0' : τ _,
        @finite_family_succ_path
          (@comm_ring_carrier R) (@nat_add m0 n)
          (@comm_ring_vector_append R (succ m0) n
            (@comm_ring_vector_add R (succ m0) u0 u0')
            (@comm_ring_vector_add R n v0 v0'))
          (@comm_ring_vector_add R (@nat_add (succ m0) n)
            (@comm_ring_vector_append R (succ m0) n u0 v0)
            (@comm_ring_vector_append R (succ m0) n u0' v0'))
          (@eq_refl
            (@comm_ring_carrier R)
            (@comm_ring_add R
              (@finite_family_head (@comm_ring_carrier R) m0 u0)
              (@finite_family_head (@comm_ring_carrier R) m0 u0')))
          (ih
            (@finite_family_tail (@comm_ring_carrier R) m0 u0)
            (@finite_family_tail (@comm_ring_carrier R) m0 u0')
            v0 v0'))
    m) u u' v v';

// Concatenation commutes with componentwise scalar multiplication.
symbol comm_ring_vector_scale_append_path
  (R : τ CommRing)
  (m n : τ Nat_grpd)
  (a : τ (@comm_ring_carrier R))
  (u : τ (@CommRingVector R m))
  (v : τ (@CommRingVector R n))
  : τ (@= (@CommRingVector R (@nat_add m n))
      (@comm_ring_vector_scale R (@nat_add m n) a
        (@comm_ring_vector_append R m n u v))
      (@comm_ring_vector_append R m n
        (@comm_ring_vector_scale R m a u)
        (@comm_ring_vector_scale R n a v)))
≔ (@nat_elim
    (λ m0 : τ Nat_grpd,
      @Pi_grpd (@CommRingVector R m0) (λ u0 : τ _,
        @Pi_grpd (@CommRingVector R n) (λ v0 : τ _,
          @= (@CommRingVector R (@nat_add m0 n))
            (@comm_ring_vector_scale R (@nat_add m0 n) a
              (@comm_ring_vector_append R m0 n u0 v0))
            (@comm_ring_vector_append R m0 n
              (@comm_ring_vector_scale R m0 a u0)
              (@comm_ring_vector_scale R n a v0)))))
    (λ _ : τ _, λ v0 : τ _,
      @eq_refl
        (@CommRingVector R n)
        (@comm_ring_vector_scale R n a v0))
    (λ m0 : τ Nat_grpd, λ ih : τ _,
      λ u0 : τ _, λ v0 : τ _,
        @finite_family_succ_path
          (@comm_ring_carrier R) (@nat_add m0 n)
          (@comm_ring_vector_scale R (@nat_add (succ m0) n) a
            (@comm_ring_vector_append R (succ m0) n u0 v0))
          (@comm_ring_vector_append R (succ m0) n
            (@comm_ring_vector_scale R (succ m0) a u0)
            (@comm_ring_vector_scale R n a v0))
          (@eq_refl
            (@comm_ring_carrier R)
            (@comm_ring_mul R a
              (@finite_family_head (@comm_ring_carrier R) m0 u0)))
          (ih
            (@finite_family_tail (@comm_ring_carrier R) m0 u0)
            v0))
    m) u v;

// Horizontal block application splits as the sum of the two block actions.
symbol comm_ring_matrix_horizontal_apply_path
  (R : τ CommRing)
  (rows columns_left columns_right : τ Nat_grpd)
  (A : τ (@CommRingMatrix R rows columns_left))
  (B : τ (@CommRingMatrix R rows columns_right))
  (u : τ (@CommRingVector R columns_left))
  (v : τ (@CommRingVector R columns_right))
  : τ (@= (@CommRingVector R rows)
      (@comm_ring_matrix_apply R rows
        (@nat_add columns_left columns_right)
        (@comm_ring_matrix_horizontal
          R rows columns_left columns_right A B)
        (@comm_ring_vector_append R columns_left columns_right u v))
      (@comm_ring_vector_add R rows
        (@comm_ring_matrix_apply R rows columns_left A u)
        (@comm_ring_matrix_apply R rows columns_right B v)))
≔ (@nat_elim
    (λ columns_left0 : τ Nat_grpd,
      @Pi_grpd (@CommRingMatrix R rows columns_left0) (λ A0 : τ _,
        @Pi_grpd (@CommRingVector R columns_left0) (λ u0 : τ _,
          @= (@CommRingVector R rows)
            (@comm_ring_matrix_apply R rows
              (@nat_add columns_left0 columns_right)
              (@comm_ring_matrix_horizontal
                R rows columns_left0 columns_right A0 B)
              (@comm_ring_vector_append
                R columns_left0 columns_right u0 v))
            (@comm_ring_vector_add R rows
              (@comm_ring_matrix_apply R rows columns_left0 A0 u0)
              (@comm_ring_matrix_apply R rows columns_right B v)))))
    (λ _ : τ _, λ _ : τ _,
      @eq_sym
        (@CommRingVector R rows)
        (@comm_ring_vector_add R rows
          (@comm_ring_vector_zero R rows)
          (@comm_ring_matrix_apply R rows columns_right B v))
        (@comm_ring_matrix_apply R rows columns_right B v)
        (@comm_ring_vector_add_zero_left_path R rows
          (@comm_ring_matrix_apply R rows columns_right B v)))
    (λ columns_left0 : τ Nat_grpd, λ ih : τ _,
      λ A0 : τ _, λ u0 : τ _,
        @eq_trans
          (@CommRingVector R rows)
          (@comm_ring_matrix_apply R rows
            (@nat_add (succ columns_left0) columns_right)
            (@comm_ring_matrix_horizontal R rows
              (succ columns_left0) columns_right A0 B)
            (@comm_ring_vector_append R
              (succ columns_left0) columns_right u0 v))
          (@comm_ring_vector_add R rows
            (@comm_ring_vector_scale R rows
              (@finite_family_head
                (@comm_ring_carrier R) columns_left0 u0)
              (@finite_family_head
                (@CommRingVector R rows) columns_left0 A0))
            (@comm_ring_vector_add R rows
              (@comm_ring_matrix_apply R rows columns_left0
                (@finite_family_tail
                  (@CommRingVector R rows) columns_left0 A0)
                (@finite_family_tail
                  (@comm_ring_carrier R) columns_left0 u0))
              (@comm_ring_matrix_apply R rows columns_right B v)))
          (@comm_ring_vector_add R rows
            (@comm_ring_matrix_apply R rows (succ columns_left0) A0 u0)
            (@comm_ring_matrix_apply R rows columns_right B v))
          (@eq_ap
            (@CommRingVector R rows)
            (@CommRingVector R rows)
            (λ tail : τ (@CommRingVector R rows),
              @comm_ring_vector_add R rows
                (@comm_ring_vector_scale R rows
                  (@finite_family_head
                    (@comm_ring_carrier R) columns_left0 u0)
                  (@finite_family_head
                    (@CommRingVector R rows) columns_left0 A0))
                tail)
            (@comm_ring_matrix_apply R rows
              (@nat_add columns_left0 columns_right)
              (@comm_ring_matrix_horizontal R rows
                columns_left0 columns_right
                (@finite_family_tail
                  (@CommRingVector R rows) columns_left0 A0)
                B)
              (@comm_ring_vector_append R columns_left0 columns_right
                (@finite_family_tail
                  (@comm_ring_carrier R) columns_left0 u0)
                v))
            (@comm_ring_vector_add R rows
              (@comm_ring_matrix_apply R rows columns_left0
                (@finite_family_tail
                  (@CommRingVector R rows) columns_left0 A0)
                (@finite_family_tail
                  (@comm_ring_carrier R) columns_left0 u0))
              (@comm_ring_matrix_apply R rows columns_right B v))
            (ih
              (@finite_family_tail
                (@CommRingVector R rows) columns_left0 A0)
              (@finite_family_tail
                (@comm_ring_carrier R) columns_left0 u0)))
          (@eq_sym
            (@CommRingVector R rows)
            (@comm_ring_vector_add R rows
              (@comm_ring_vector_add R rows
                (@comm_ring_vector_scale R rows
                  (@finite_family_head
                    (@comm_ring_carrier R) columns_left0 u0)
                  (@finite_family_head
                    (@CommRingVector R rows) columns_left0 A0))
                (@comm_ring_matrix_apply R rows columns_left0
                  (@finite_family_tail
                    (@CommRingVector R rows) columns_left0 A0)
                  (@finite_family_tail
                    (@comm_ring_carrier R) columns_left0 u0)))
              (@comm_ring_matrix_apply R rows columns_right B v))
            (@comm_ring_vector_add R rows
              (@comm_ring_vector_scale R rows
                (@finite_family_head
                  (@comm_ring_carrier R) columns_left0 u0)
                (@finite_family_head
                  (@CommRingVector R rows) columns_left0 A0))
              (@comm_ring_vector_add R rows
                (@comm_ring_matrix_apply R rows columns_left0
                  (@finite_family_tail
                    (@CommRingVector R rows) columns_left0 A0)
                  (@finite_family_tail
                    (@comm_ring_carrier R) columns_left0 u0))
                (@comm_ring_matrix_apply R rows columns_right B v)))
            (@comm_ring_vector_add_assoc_path R rows
              (@comm_ring_vector_scale R rows
                (@finite_family_head
                  (@comm_ring_carrier R) columns_left0 u0)
                (@finite_family_head
                  (@CommRingVector R rows) columns_left0 A0))
              (@comm_ring_matrix_apply R rows columns_left0
                (@finite_family_tail
                  (@CommRingVector R rows) columns_left0 A0)
                (@finite_family_tail
                  (@comm_ring_carrier R) columns_left0 u0))
              (@comm_ring_matrix_apply R rows columns_right B v))))
    columns_left) A u;

// Vertical block application is vector concatenation of the two actions.
symbol comm_ring_matrix_vertical_apply_path
  (R : τ CommRing)
  (rows_top rows_bottom columns : τ Nat_grpd)
  (A : τ (@CommRingMatrix R rows_top columns))
  (B : τ (@CommRingMatrix R rows_bottom columns))
  (x : τ (@CommRingVector R columns))
  : τ (@= (@CommRingVector R (@nat_add rows_top rows_bottom))
      (@comm_ring_matrix_apply R (@nat_add rows_top rows_bottom) columns
        (@comm_ring_matrix_vertical
          R rows_top rows_bottom columns A B)
        x)
      (@comm_ring_vector_append R rows_top rows_bottom
        (@comm_ring_matrix_apply R rows_top columns A x)
        (@comm_ring_matrix_apply R rows_bottom columns B x)))
≔ (@nat_elim
    (λ columns0 : τ Nat_grpd,
      @Pi_grpd (@CommRingMatrix R rows_top columns0) (λ A0 : τ _,
        @Pi_grpd (@CommRingMatrix R rows_bottom columns0) (λ B0 : τ _,
          @Pi_grpd (@CommRingVector R columns0) (λ x0 : τ _,
            @= (@CommRingVector R (@nat_add rows_top rows_bottom))
              (@comm_ring_matrix_apply R
                (@nat_add rows_top rows_bottom) columns0
                (@comm_ring_matrix_vertical R rows_top rows_bottom
                  columns0 A0 B0)
                x0)
              (@comm_ring_vector_append R rows_top rows_bottom
                (@comm_ring_matrix_apply R rows_top columns0 A0 x0)
                (@comm_ring_matrix_apply R rows_bottom columns0 B0 x0))))))
    (λ _ : τ _, λ _ : τ _, λ _ : τ _,
      @eq_sym
        (@CommRingVector R (@nat_add rows_top rows_bottom))
        (@comm_ring_vector_append R rows_top rows_bottom
          (@comm_ring_vector_zero R rows_top)
          (@comm_ring_vector_zero R rows_bottom))
        (@comm_ring_vector_zero R (@nat_add rows_top rows_bottom))
        (@comm_ring_vector_append_zero_path R rows_top rows_bottom))
    (λ columns0 : τ Nat_grpd, λ ih : τ _,
      λ A0 : τ _, λ B0 : τ _, λ x0 : τ _,
        @eq_trans
          (@CommRingVector R (@nat_add rows_top rows_bottom))
          (@comm_ring_matrix_apply R
            (@nat_add rows_top rows_bottom) (succ columns0)
            (@comm_ring_matrix_vertical R rows_top rows_bottom
              (succ columns0) A0 B0)
            x0)
          (@comm_ring_vector_add R (@nat_add rows_top rows_bottom)
            (@comm_ring_vector_append R rows_top rows_bottom
              (@comm_ring_vector_scale R rows_top
                (@finite_family_head
                  (@comm_ring_carrier R) columns0 x0)
                (@finite_family_head
                  (@CommRingVector R rows_top) columns0 A0))
              (@comm_ring_vector_scale R rows_bottom
                (@finite_family_head
                  (@comm_ring_carrier R) columns0 x0)
                (@finite_family_head
                  (@CommRingVector R rows_bottom) columns0 B0)))
            (@comm_ring_vector_append R rows_top rows_bottom
              (@comm_ring_matrix_apply R rows_top columns0
                (@finite_family_tail
                  (@CommRingVector R rows_top) columns0 A0)
                (@finite_family_tail
                  (@comm_ring_carrier R) columns0 x0))
              (@comm_ring_matrix_apply R rows_bottom columns0
                (@finite_family_tail
                  (@CommRingVector R rows_bottom) columns0 B0)
                (@finite_family_tail
                  (@comm_ring_carrier R) columns0 x0))))
          (@comm_ring_vector_append R rows_top rows_bottom
            (@comm_ring_matrix_apply R rows_top (succ columns0) A0 x0)
            (@comm_ring_matrix_apply R rows_bottom (succ columns0) B0 x0))
          (@comm_ring_vector_add_congr_path
            R (@nat_add rows_top rows_bottom)
            (@comm_ring_vector_scale R (@nat_add rows_top rows_bottom)
              (@finite_family_head
                (@comm_ring_carrier R) columns0 x0)
              (@comm_ring_vector_append R rows_top rows_bottom
                (@finite_family_head
                  (@CommRingVector R rows_top) columns0 A0)
                (@finite_family_head
                  (@CommRingVector R rows_bottom) columns0 B0)))
            (@comm_ring_vector_append R rows_top rows_bottom
              (@comm_ring_vector_scale R rows_top
                (@finite_family_head
                  (@comm_ring_carrier R) columns0 x0)
                (@finite_family_head
                  (@CommRingVector R rows_top) columns0 A0))
              (@comm_ring_vector_scale R rows_bottom
                (@finite_family_head
                  (@comm_ring_carrier R) columns0 x0)
                (@finite_family_head
                  (@CommRingVector R rows_bottom) columns0 B0)))
            (@comm_ring_matrix_apply R (@nat_add rows_top rows_bottom)
              columns0
              (@comm_ring_matrix_vertical R rows_top rows_bottom columns0
                (@finite_family_tail
                  (@CommRingVector R rows_top) columns0 A0)
                (@finite_family_tail
                  (@CommRingVector R rows_bottom) columns0 B0))
              (@finite_family_tail
                (@comm_ring_carrier R) columns0 x0))
            (@comm_ring_vector_append R rows_top rows_bottom
              (@comm_ring_matrix_apply R rows_top columns0
                (@finite_family_tail
                  (@CommRingVector R rows_top) columns0 A0)
                (@finite_family_tail
                  (@comm_ring_carrier R) columns0 x0))
              (@comm_ring_matrix_apply R rows_bottom columns0
                (@finite_family_tail
                  (@CommRingVector R rows_bottom) columns0 B0)
                (@finite_family_tail
                  (@comm_ring_carrier R) columns0 x0)))
            (@comm_ring_vector_scale_append_path
              R rows_top rows_bottom
              (@finite_family_head
                (@comm_ring_carrier R) columns0 x0)
              (@finite_family_head
                (@CommRingVector R rows_top) columns0 A0)
              (@finite_family_head
                (@CommRingVector R rows_bottom) columns0 B0))
            (ih
              (@finite_family_tail
                (@CommRingVector R rows_top) columns0 A0)
              (@finite_family_tail
                (@CommRingVector R rows_bottom) columns0 B0)
              (@finite_family_tail
                (@comm_ring_carrier R) columns0 x0)))
          (@eq_sym
            (@CommRingVector R (@nat_add rows_top rows_bottom))
            (@comm_ring_vector_append R rows_top rows_bottom
              (@comm_ring_vector_add R rows_top
                (@comm_ring_vector_scale R rows_top
                  (@finite_family_head
                    (@comm_ring_carrier R) columns0 x0)
                  (@finite_family_head
                    (@CommRingVector R rows_top) columns0 A0))
                (@comm_ring_matrix_apply R rows_top columns0
                  (@finite_family_tail
                    (@CommRingVector R rows_top) columns0 A0)
                  (@finite_family_tail
                    (@comm_ring_carrier R) columns0 x0)))
              (@comm_ring_vector_add R rows_bottom
                (@comm_ring_vector_scale R rows_bottom
                  (@finite_family_head
                    (@comm_ring_carrier R) columns0 x0)
                  (@finite_family_head
                    (@CommRingVector R rows_bottom) columns0 B0))
                (@comm_ring_matrix_apply R rows_bottom columns0
                  (@finite_family_tail
                    (@CommRingVector R rows_bottom) columns0 B0)
                  (@finite_family_tail
                    (@comm_ring_carrier R) columns0 x0))))
            (@comm_ring_vector_add R (@nat_add rows_top rows_bottom)
              (@comm_ring_vector_append R rows_top rows_bottom
                (@comm_ring_vector_scale R rows_top
                  (@finite_family_head
                    (@comm_ring_carrier R) columns0 x0)
                  (@finite_family_head
                    (@CommRingVector R rows_top) columns0 A0))
                (@comm_ring_vector_scale R rows_bottom
                  (@finite_family_head
                    (@comm_ring_carrier R) columns0 x0)
                  (@finite_family_head
                    (@CommRingVector R rows_bottom) columns0 B0)))
              (@comm_ring_vector_append R rows_top rows_bottom
                (@comm_ring_matrix_apply R rows_top columns0
                  (@finite_family_tail
                    (@CommRingVector R rows_top) columns0 A0)
                  (@finite_family_tail
                    (@comm_ring_carrier R) columns0 x0))
                (@comm_ring_matrix_apply R rows_bottom columns0
                  (@finite_family_tail
                    (@CommRingVector R rows_bottom) columns0 B0)
                  (@finite_family_tail
                    (@comm_ring_carrier R) columns0 x0))))
            (@comm_ring_vector_append_add_path
              R rows_top rows_bottom
              (@comm_ring_vector_scale R rows_top
                (@finite_family_head
                  (@comm_ring_carrier R) columns0 x0)
                (@finite_family_head
                  (@CommRingVector R rows_top) columns0 A0))
              (@comm_ring_matrix_apply R rows_top columns0
                (@finite_family_tail
                  (@CommRingVector R rows_top) columns0 A0)
                (@finite_family_tail
                  (@comm_ring_carrier R) columns0 x0))
              (@comm_ring_vector_scale R rows_bottom
                (@finite_family_head
                  (@comm_ring_carrier R) columns0 x0)
                (@finite_family_head
                  (@CommRingVector R rows_bottom) columns0 B0))
              (@comm_ring_matrix_apply R rows_bottom columns0
                (@finite_family_tail
                  (@CommRingVector R rows_bottom) columns0 B0)
                (@finite_family_tail
                  (@comm_ring_carrier R) columns0 x0)))))
    columns) A B x;

// View one vector as a one-column matrix.
symbol comm_ring_vector_single_column
  (R : τ CommRing)
  (rows : τ Nat_grpd)
  (u : τ (@CommRingVector R rows))
  : τ (@CommRingMatrix R rows (succ zero))
≔ @finite_family_cons
    (@CommRingVector R rows) zero u
    (@finite_family_nil (@CommRingVector R rows));

// The stable finite-free identity matrix acts as the identity on vectors.
symbol comm_ring_matrix_apply_id_path
  (R : τ CommRing)
  (rows : τ Nat_grpd)
  (u : τ (@CommRingVector R rows))
  : τ (@= (@CommRingVector R rows)
      (@comm_ring_matrix_apply R rows rows
        (@comm_ring_finite_free_id_matrix R rows) u)
      u)
≔ @eq_ap
    (@CommRingMatrix R rows (succ zero))
    (@CommRingVector R rows)
    (λ M : τ (@CommRingMatrix R rows (succ zero)),
      @finite_family_head (@CommRingVector R rows) zero M)
    (@comm_ring_matrix_comp R rows rows (succ zero)
      (@comm_ring_finite_free_id_matrix R rows)
      (@comm_ring_vector_single_column R rows u))
    (@comm_ring_vector_single_column R rows u)
    (@comm_ring_matrix_comp_left_identity_path R (succ zero) rows
      (@comm_ring_vector_single_column R rows u));

// First block projection applied to a concatenated vector returns its left part.
symbol comm_ring_matrix_proj1_apply_path
  (R : τ CommRing)
  (m n : τ Nat_grpd)
  (u : τ (@CommRingVector R m))
  (v : τ (@CommRingVector R n))
  : τ (@= (@CommRingVector R m)
      (@comm_ring_matrix_apply R m (@nat_add m n)
        (@comm_ring_matrix_proj1 R m n)
        (@comm_ring_vector_append R m n u v))
      u)
≔ @eq_trans
    (@CommRingVector R m)
    (@comm_ring_matrix_apply R m (@nat_add m n)
      (@comm_ring_matrix_proj1 R m n)
      (@comm_ring_vector_append R m n u v))
    (@comm_ring_vector_add R m u (@comm_ring_vector_zero R m))
    u
    (@eq_trans
      (@CommRingVector R m)
      (@comm_ring_matrix_apply R m (@nat_add m n)
        (@comm_ring_matrix_proj1 R m n)
        (@comm_ring_vector_append R m n u v))
      (@comm_ring_vector_add R m
        (@comm_ring_matrix_apply R m m
          (@comm_ring_finite_free_id_matrix R m) u)
        (@comm_ring_matrix_apply R m n
          (@comm_ring_matrix_zero R m n) v))
      (@comm_ring_vector_add R m u (@comm_ring_vector_zero R m))
      (@comm_ring_matrix_horizontal_apply_path R m m n
        (@comm_ring_finite_free_id_matrix R m)
        (@comm_ring_matrix_zero R m n) u v)
      (@comm_ring_vector_add_congr_path R m
        (@comm_ring_matrix_apply R m m
          (@comm_ring_finite_free_id_matrix R m) u)
        u
        (@comm_ring_matrix_apply R m n
          (@comm_ring_matrix_zero R m n) v)
        (@comm_ring_vector_zero R m)
        (@comm_ring_matrix_apply_id_path R m u)
        (@comm_ring_matrix_apply_zero_matrix_path R m n v)))
    (@comm_ring_vector_add_zero_right_path R m u);

// Second block projection applied to a concatenated vector returns its right part.
symbol comm_ring_matrix_proj2_apply_path
  (R : τ CommRing)
  (m n : τ Nat_grpd)
  (u : τ (@CommRingVector R m))
  (v : τ (@CommRingVector R n))
  : τ (@= (@CommRingVector R n)
      (@comm_ring_matrix_apply R n (@nat_add m n)
        (@comm_ring_matrix_proj2 R m n)
        (@comm_ring_vector_append R m n u v))
      v)
≔ @eq_trans
    (@CommRingVector R n)
    (@comm_ring_matrix_apply R n (@nat_add m n)
      (@comm_ring_matrix_proj2 R m n)
      (@comm_ring_vector_append R m n u v))
    (@comm_ring_vector_add R n (@comm_ring_vector_zero R n) v)
    v
    (@eq_trans
      (@CommRingVector R n)
      (@comm_ring_matrix_apply R n (@nat_add m n)
        (@comm_ring_matrix_proj2 R m n)
        (@comm_ring_vector_append R m n u v))
      (@comm_ring_vector_add R n
        (@comm_ring_matrix_apply R n m
          (@comm_ring_matrix_zero R n m) u)
        (@comm_ring_matrix_apply R n n
          (@comm_ring_finite_free_id_matrix R n) v))
      (@comm_ring_vector_add R n (@comm_ring_vector_zero R n) v)
      (@comm_ring_matrix_horizontal_apply_path R n m n
        (@comm_ring_matrix_zero R n m)
        (@comm_ring_finite_free_id_matrix R n) u v)
      (@comm_ring_vector_add_congr_path R n
        (@comm_ring_matrix_apply R n m
          (@comm_ring_matrix_zero R n m) u)
        (@comm_ring_vector_zero R n)
        (@comm_ring_matrix_apply R n n
          (@comm_ring_finite_free_id_matrix R n) v)
        v
        (@comm_ring_matrix_apply_zero_matrix_path R n m u)
        (@comm_ring_matrix_apply_id_path R n v)))
    (@comm_ring_vector_add_zero_left_path R n v);

// First projection applied to an arbitrary direct-sum vector selects `take`.
symbol comm_ring_matrix_proj1_apply_any_path
  (R : τ CommRing)
  (m n : τ Nat_grpd)
  (w : τ (@CommRingVector R (@nat_add m n)))
  : τ (@= (@CommRingVector R m)
      (@comm_ring_matrix_apply R m (@nat_add m n)
        (@comm_ring_matrix_proj1 R m n) w)
      (@comm_ring_vector_take_left R m n w))
≔ @eq_trans
    (@CommRingVector R m)
    (@comm_ring_matrix_apply R m (@nat_add m n)
      (@comm_ring_matrix_proj1 R m n) w)
    (@comm_ring_matrix_apply R m (@nat_add m n)
      (@comm_ring_matrix_proj1 R m n)
      (@comm_ring_vector_append R m n
        (@comm_ring_vector_take_left R m n w)
        (@comm_ring_vector_drop_left R m n w)))
    (@comm_ring_vector_take_left R m n w)
    (@eq_ap
      (@CommRingVector R (@nat_add m n))
      (@CommRingVector R m)
      (λ z : τ (@CommRingVector R (@nat_add m n)),
        @comm_ring_matrix_apply R m (@nat_add m n)
          (@comm_ring_matrix_proj1 R m n) z)
      w
      (@comm_ring_vector_append R m n
        (@comm_ring_vector_take_left R m n w)
        (@comm_ring_vector_drop_left R m n w))
      (@eq_sym
        (@CommRingVector R (@nat_add m n))
        (@comm_ring_vector_append R m n
          (@comm_ring_vector_take_left R m n w)
          (@comm_ring_vector_drop_left R m n w))
        w
        (@finite_family_append_split_path
          (@comm_ring_carrier R) m n w)))
    (@comm_ring_matrix_proj1_apply_path R m n
      (@comm_ring_vector_take_left R m n w)
      (@comm_ring_vector_drop_left R m n w));

// Second projection applied to an arbitrary direct-sum vector selects `drop`.
symbol comm_ring_matrix_proj2_apply_any_path
  (R : τ CommRing)
  (m n : τ Nat_grpd)
  (w : τ (@CommRingVector R (@nat_add m n)))
  : τ (@= (@CommRingVector R n)
      (@comm_ring_matrix_apply R n (@nat_add m n)
        (@comm_ring_matrix_proj2 R m n) w)
      (@comm_ring_vector_drop_left R m n w))
≔ @eq_trans
    (@CommRingVector R n)
    (@comm_ring_matrix_apply R n (@nat_add m n)
      (@comm_ring_matrix_proj2 R m n) w)
    (@comm_ring_matrix_apply R n (@nat_add m n)
      (@comm_ring_matrix_proj2 R m n)
      (@comm_ring_vector_append R m n
        (@comm_ring_vector_take_left R m n w)
        (@comm_ring_vector_drop_left R m n w)))
    (@comm_ring_vector_drop_left R m n w)
    (@eq_ap
      (@CommRingVector R (@nat_add m n))
      (@CommRingVector R n)
      (λ z : τ (@CommRingVector R (@nat_add m n)),
        @comm_ring_matrix_apply R n (@nat_add m n)
          (@comm_ring_matrix_proj2 R m n) z)
      w
      (@comm_ring_vector_append R m n
        (@comm_ring_vector_take_left R m n w)
        (@comm_ring_vector_drop_left R m n w))
      (@eq_sym
        (@CommRingVector R (@nat_add m n))
        (@comm_ring_vector_append R m n
          (@comm_ring_vector_take_left R m n w)
          (@comm_ring_vector_drop_left R m n w))
        w
        (@finite_family_append_split_path
          (@comm_ring_carrier R) m n w)))
    (@comm_ring_matrix_proj2_apply_path R m n
      (@comm_ring_vector_take_left R m n w)
      (@comm_ring_vector_drop_left R m n w));

// First projection after vertical pairing is the first matrix.
symbol comm_ring_matrix_proj1_vertical_path
  (R : τ CommRing)
  (m n columns : τ Nat_grpd)
  (F : τ (@CommRingMatrix R m columns))
  (G : τ (@CommRingMatrix R n columns))
  : τ (@= (@CommRingMatrix R m columns)
      (@comm_ring_matrix_comp R m (@nat_add m n) columns
        (@comm_ring_matrix_proj1 R m n)
        (@comm_ring_matrix_vertical R m n columns F G))
      F)
≔ (@nat_elim
    (λ columns0 : τ Nat_grpd,
      @Pi_grpd (@CommRingMatrix R m columns0) (λ F0 : τ _,
        @Pi_grpd (@CommRingMatrix R n columns0) (λ G0 : τ _,
          @= (@CommRingMatrix R m columns0)
            (@comm_ring_matrix_comp R m (@nat_add m n) columns0
              (@comm_ring_matrix_proj1 R m n)
              (@comm_ring_matrix_vertical R m n columns0 F0 G0))
            F0)))
    (λ F0 : τ _, λ _ : τ _,
      (sigma_Snd unit_is_contr) F0)
    (λ columns0 : τ Nat_grpd, λ ih : τ _,
      λ F0 : τ _, λ G0 : τ _,
        @finite_family_succ_path
          (@CommRingVector R m) columns0
          (@comm_ring_matrix_comp R m (@nat_add m n) (succ columns0)
            (@comm_ring_matrix_proj1 R m n)
            (@comm_ring_matrix_vertical R m n (succ columns0) F0 G0))
          F0
          (@comm_ring_matrix_proj1_apply_path R m n
            (@finite_family_head (@CommRingVector R m) columns0 F0)
            (@finite_family_head (@CommRingVector R n) columns0 G0))
          (ih
            (@finite_family_tail (@CommRingVector R m) columns0 F0)
            (@finite_family_tail (@CommRingVector R n) columns0 G0)))
    columns) F G;

// Second projection after vertical pairing is the second matrix.
symbol comm_ring_matrix_proj2_vertical_path
  (R : τ CommRing)
  (m n columns : τ Nat_grpd)
  (F : τ (@CommRingMatrix R m columns))
  (G : τ (@CommRingMatrix R n columns))
  : τ (@= (@CommRingMatrix R n columns)
      (@comm_ring_matrix_comp R n (@nat_add m n) columns
        (@comm_ring_matrix_proj2 R m n)
        (@comm_ring_matrix_vertical R m n columns F G))
      G)
≔ (@nat_elim
    (λ columns0 : τ Nat_grpd,
      @Pi_grpd (@CommRingMatrix R m columns0) (λ F0 : τ _,
        @Pi_grpd (@CommRingMatrix R n columns0) (λ G0 : τ _,
          @= (@CommRingMatrix R n columns0)
            (@comm_ring_matrix_comp R n (@nat_add m n) columns0
              (@comm_ring_matrix_proj2 R m n)
              (@comm_ring_matrix_vertical R m n columns0 F0 G0))
            G0)))
    (λ _ : τ _, λ G0 : τ _,
      (sigma_Snd unit_is_contr) G0)
    (λ columns0 : τ Nat_grpd, λ ih : τ _,
      λ F0 : τ _, λ G0 : τ _,
        @finite_family_succ_path
          (@CommRingVector R n) columns0
          (@comm_ring_matrix_comp R n (@nat_add m n) (succ columns0)
            (@comm_ring_matrix_proj2 R m n)
            (@comm_ring_matrix_vertical R m n (succ columns0) F0 G0))
          G0
          (@comm_ring_matrix_proj2_apply_path R m n
            (@finite_family_head (@CommRingVector R m) columns0 F0)
            (@finite_family_head (@CommRingVector R n) columns0 G0))
          (ih
            (@finite_family_tail (@CommRingVector R m) columns0 F0)
            (@finite_family_tail (@CommRingVector R n) columns0 G0)))
    columns) F G;

// Pairing the two projection composites reconstructs an arbitrary matrix.
symbol comm_ring_matrix_vertical_proj_eta_path
  (R : τ CommRing)
  (m n columns : τ Nat_grpd)
  (H : τ (@CommRingMatrix R (@nat_add m n) columns))
  : τ (@= (@CommRingMatrix R (@nat_add m n) columns)
      (@comm_ring_matrix_vertical R m n columns
        (@comm_ring_matrix_comp R m (@nat_add m n) columns
          (@comm_ring_matrix_proj1 R m n) H)
        (@comm_ring_matrix_comp R n (@nat_add m n) columns
          (@comm_ring_matrix_proj2 R m n) H))
      H)
≔ (@nat_elim
    (λ columns0 : τ Nat_grpd,
      @Pi_grpd (@CommRingMatrix R (@nat_add m n) columns0) (λ H0 : τ _,
        @= (@CommRingMatrix R (@nat_add m n) columns0)
          (@comm_ring_matrix_vertical R m n columns0
            (@comm_ring_matrix_comp R m (@nat_add m n) columns0
              (@comm_ring_matrix_proj1 R m n) H0)
            (@comm_ring_matrix_comp R n (@nat_add m n) columns0
              (@comm_ring_matrix_proj2 R m n) H0))
          H0))
    (λ H0 : τ _, (sigma_Snd unit_is_contr) H0)
    (λ columns0 : τ Nat_grpd, λ ih : τ _, λ H0 : τ _,
      @finite_family_succ_path
        (@CommRingVector R (@nat_add m n)) columns0
        (@comm_ring_matrix_vertical R m n (succ columns0)
          (@comm_ring_matrix_comp R m (@nat_add m n) (succ columns0)
            (@comm_ring_matrix_proj1 R m n) H0)
          (@comm_ring_matrix_comp R n (@nat_add m n) (succ columns0)
            (@comm_ring_matrix_proj2 R m n) H0))
        H0
        (@eq_trans
          (@CommRingVector R (@nat_add m n))
          (@comm_ring_vector_append R m n
            (@comm_ring_matrix_apply R m (@nat_add m n)
              (@comm_ring_matrix_proj1 R m n)
              (@finite_family_head
                (@CommRingVector R (@nat_add m n)) columns0 H0))
            (@comm_ring_matrix_apply R n (@nat_add m n)
              (@comm_ring_matrix_proj2 R m n)
              (@finite_family_head
                (@CommRingVector R (@nat_add m n)) columns0 H0)))
          (@comm_ring_vector_append R m n
            (@comm_ring_vector_take_left R m n
              (@finite_family_head
                (@CommRingVector R (@nat_add m n)) columns0 H0))
            (@comm_ring_vector_drop_left R m n
              (@finite_family_head
                (@CommRingVector R (@nat_add m n)) columns0 H0)))
          (@finite_family_head
            (@CommRingVector R (@nat_add m n)) columns0 H0)
          (@comm_ring_vector_append_congr_path R m n
            (@comm_ring_matrix_apply R m (@nat_add m n)
              (@comm_ring_matrix_proj1 R m n)
              (@finite_family_head
                (@CommRingVector R (@nat_add m n)) columns0 H0))
            (@comm_ring_vector_take_left R m n
              (@finite_family_head
                (@CommRingVector R (@nat_add m n)) columns0 H0))
            (@comm_ring_matrix_apply R n (@nat_add m n)
              (@comm_ring_matrix_proj2 R m n)
              (@finite_family_head
                (@CommRingVector R (@nat_add m n)) columns0 H0))
            (@comm_ring_vector_drop_left R m n
              (@finite_family_head
                (@CommRingVector R (@nat_add m n)) columns0 H0))
            (@comm_ring_matrix_proj1_apply_any_path R m n
              (@finite_family_head
                (@CommRingVector R (@nat_add m n)) columns0 H0))
            (@comm_ring_matrix_proj2_apply_any_path R m n
              (@finite_family_head
                (@CommRingVector R (@nat_add m n)) columns0 H0)))
          (@finite_family_append_split_path
            (@comm_ring_carrier R) m n
            (@finite_family_head
              (@CommRingVector R (@nat_add m n)) columns0 H0)))
        (ih
          (@finite_family_tail
            (@CommRingVector R (@nat_add m n)) columns0 H0)))
    columns) H;

// Congruence of horizontal matrix blocks.
symbol comm_ring_matrix_horizontal_congr_path
  (R : τ CommRing)
  (rows columns_left columns_right : τ Nat_grpd)
  (A A' : τ (@CommRingMatrix R rows columns_left))
  (B B' : τ (@CommRingMatrix R rows columns_right))
  (p : τ (@= (@CommRingMatrix R rows columns_left) A A'))
  (q : τ (@= (@CommRingMatrix R rows columns_right) B B'))
  : τ (@= (@CommRingMatrix R rows
      (@nat_add columns_left columns_right))
      (@comm_ring_matrix_horizontal
        R rows columns_left columns_right A B)
      (@comm_ring_matrix_horizontal
        R rows columns_left columns_right A' B'))
≔ @finite_family_append_congr_path
    (@CommRingVector R rows)
    columns_left columns_right A A' B B' p q;

// Congruence of vertical matrix blocks.
symbol comm_ring_matrix_vertical_congr_path
  (R : τ CommRing)
  (rows_top rows_bottom columns : τ Nat_grpd)
  (A A' : τ (@CommRingMatrix R rows_top columns))
  (B B' : τ (@CommRingMatrix R rows_bottom columns))
  (p : τ (@= (@CommRingMatrix R rows_top columns) A A'))
  (q : τ (@= (@CommRingMatrix R rows_bottom columns) B B'))
  : τ (@= (@CommRingMatrix R (@nat_add rows_top rows_bottom) columns)
      (@comm_ring_matrix_vertical R rows_top rows_bottom columns A B)
      (@comm_ring_matrix_vertical R rows_top rows_bottom columns A' B'))
≔ @eq_trans
    (@CommRingMatrix R (@nat_add rows_top rows_bottom) columns)
    (@comm_ring_matrix_vertical R rows_top rows_bottom columns A B)
    (@comm_ring_matrix_vertical R rows_top rows_bottom columns A' B)
    (@comm_ring_matrix_vertical R rows_top rows_bottom columns A' B')
    (@eq_ap
      (@CommRingMatrix R rows_top columns)
      (@CommRingMatrix R (@nat_add rows_top rows_bottom) columns)
      (λ M : τ (@CommRingMatrix R rows_top columns),
        @comm_ring_matrix_vertical R rows_top rows_bottom columns M B)
      A A' p)
    (@eq_ap
      (@CommRingMatrix R rows_bottom columns)
      (@CommRingMatrix R (@nat_add rows_top rows_bottom) columns)
      (λ M : τ (@CommRingMatrix R rows_bottom columns),
        @comm_ring_matrix_vertical R rows_top rows_bottom columns A' M)
      B B' q);

// Postcomposition preserves horizontal column concatenation.
symbol comm_ring_matrix_comp_horizontal_path
  (R : τ CommRing)
  (rows middle columns_left columns_right : τ Nat_grpd)
  (A : τ (@CommRingMatrix R rows middle))
  (F : τ (@CommRingMatrix R middle columns_left))
  (G : τ (@CommRingMatrix R middle columns_right))
  : τ (@= (@CommRingMatrix R rows
      (@nat_add columns_left columns_right))
      (@comm_ring_matrix_comp R rows middle
        (@nat_add columns_left columns_right) A
        (@comm_ring_matrix_horizontal
          R middle columns_left columns_right F G))
      (@comm_ring_matrix_horizontal R rows columns_left columns_right
        (@comm_ring_matrix_comp R rows middle columns_left A F)
        (@comm_ring_matrix_comp R rows middle columns_right A G)))
≔ (@nat_elim
    (λ columns_left0 : τ Nat_grpd,
      @Pi_grpd (@CommRingMatrix R middle columns_left0) (λ F0 : τ _,
        @= (@CommRingMatrix R rows
            (@nat_add columns_left0 columns_right))
          (@comm_ring_matrix_comp R rows middle
            (@nat_add columns_left0 columns_right) A
            (@comm_ring_matrix_horizontal
              R middle columns_left0 columns_right F0 G))
          (@comm_ring_matrix_horizontal R rows
            columns_left0 columns_right
            (@comm_ring_matrix_comp R rows middle columns_left0 A F0)
            (@comm_ring_matrix_comp R rows middle columns_right A G))))
    (λ _ : τ _,
      @eq_refl
        (@CommRingMatrix R rows columns_right)
        (@comm_ring_matrix_comp R rows middle columns_right A G))
    (λ columns_left0 : τ Nat_grpd, λ ih : τ _, λ F0 : τ _,
      @finite_family_succ_path
        (@CommRingVector R rows) (@nat_add columns_left0 columns_right)
        (@comm_ring_matrix_comp R rows middle
          (@nat_add (succ columns_left0) columns_right) A
          (@comm_ring_matrix_horizontal R middle
            (succ columns_left0) columns_right F0 G))
        (@comm_ring_matrix_horizontal R rows
          (succ columns_left0) columns_right
          (@comm_ring_matrix_comp R rows middle
            (succ columns_left0) A F0)
          (@comm_ring_matrix_comp R rows middle columns_right A G))
        (@eq_refl
          (@CommRingVector R rows)
          (@comm_ring_matrix_apply R rows middle A
            (@finite_family_head
              (@CommRingVector R middle) columns_left0 F0)))
        (ih (@finite_family_tail
          (@CommRingVector R middle) columns_left0 F0)))
    columns_left) F;

// Postcomposition by a vertical block preserves vertical pairing.
symbol comm_ring_matrix_vertical_comp_path
  (R : τ CommRing)
  (rows_top rows_bottom middle columns : τ Nat_grpd)
  (A : τ (@CommRingMatrix R rows_top middle))
  (B : τ (@CommRingMatrix R rows_bottom middle))
  (H : τ (@CommRingMatrix R middle columns))
  : τ (@= (@CommRingMatrix R (@nat_add rows_top rows_bottom) columns)
      (@comm_ring_matrix_comp R (@nat_add rows_top rows_bottom)
        middle columns
        (@comm_ring_matrix_vertical R rows_top rows_bottom middle A B)
        H)
      (@comm_ring_matrix_vertical R rows_top rows_bottom columns
        (@comm_ring_matrix_comp R rows_top middle columns A H)
        (@comm_ring_matrix_comp R rows_bottom middle columns B H)))
≔ (@nat_elim
    (λ columns0 : τ Nat_grpd,
      @Pi_grpd (@CommRingMatrix R middle columns0) (λ H0 : τ _,
        @= (@CommRingMatrix R (@nat_add rows_top rows_bottom) columns0)
          (@comm_ring_matrix_comp R (@nat_add rows_top rows_bottom)
            middle columns0
            (@comm_ring_matrix_vertical R rows_top rows_bottom middle A B)
            H0)
          (@comm_ring_matrix_vertical R rows_top rows_bottom columns0
            (@comm_ring_matrix_comp R rows_top middle columns0 A H0)
            (@comm_ring_matrix_comp R rows_bottom middle columns0 B H0))))
    (λ _ : τ _,
      @eq_refl
        (@CommRingMatrix R (@nat_add rows_top rows_bottom) zero)
        (@finite_family_nil
          (@CommRingVector R (@nat_add rows_top rows_bottom))))
    (λ columns0 : τ Nat_grpd, λ ih : τ _, λ H0 : τ _,
      @finite_family_succ_path
        (@CommRingVector R (@nat_add rows_top rows_bottom)) columns0
        (@comm_ring_matrix_comp R (@nat_add rows_top rows_bottom)
          middle (succ columns0)
          (@comm_ring_matrix_vertical R rows_top rows_bottom middle A B)
          H0)
        (@comm_ring_matrix_vertical R rows_top rows_bottom (succ columns0)
          (@comm_ring_matrix_comp R rows_top middle (succ columns0) A H0)
          (@comm_ring_matrix_comp R rows_bottom middle (succ columns0) B H0))
        (@comm_ring_matrix_vertical_apply_path R rows_top rows_bottom
          middle A B
          (@finite_family_head (@CommRingVector R middle) columns0 H0))
        (ih (@finite_family_tail
          (@CommRingVector R middle) columns0 H0)))
    columns) H;

// A horizontal block after a vertical block gives the sum of diagonal actions.
symbol comm_ring_matrix_horizontal_vertical_comp_path
  (R : τ CommRing)
  (rows middle_left middle_right columns : τ Nat_grpd)
  (A : τ (@CommRingMatrix R rows middle_left))
  (B : τ (@CommRingMatrix R rows middle_right))
  (F : τ (@CommRingMatrix R middle_left columns))
  (G : τ (@CommRingMatrix R middle_right columns))
  : τ (@= (@CommRingMatrix R rows columns)
      (@comm_ring_matrix_comp R rows
        (@nat_add middle_left middle_right) columns
        (@comm_ring_matrix_horizontal
          R rows middle_left middle_right A B)
        (@comm_ring_matrix_vertical
          R middle_left middle_right columns F G))
      (@comm_ring_matrix_add R rows columns
        (@comm_ring_matrix_comp R rows middle_left columns A F)
        (@comm_ring_matrix_comp R rows middle_right columns B G)))
≔ (@nat_elim
    (λ columns0 : τ Nat_grpd,
      @Pi_grpd (@CommRingMatrix R middle_left columns0) (λ F0 : τ _,
        @Pi_grpd (@CommRingMatrix R middle_right columns0) (λ G0 : τ _,
          @= (@CommRingMatrix R rows columns0)
            (@comm_ring_matrix_comp R rows
              (@nat_add middle_left middle_right) columns0
              (@comm_ring_matrix_horizontal
                R rows middle_left middle_right A B)
              (@comm_ring_matrix_vertical
                R middle_left middle_right columns0 F0 G0))
            (@comm_ring_matrix_add R rows columns0
              (@comm_ring_matrix_comp R rows middle_left columns0 A F0)
              (@comm_ring_matrix_comp R rows middle_right columns0 B G0)))))
    (λ _ : τ _, λ _ : τ _, @eq_refl Unit_grpd tt)
    (λ columns0 : τ Nat_grpd, λ ih : τ _,
      λ F0 : τ _, λ G0 : τ _,
        @finite_family_succ_path
          (@CommRingVector R rows) columns0
          (@comm_ring_matrix_comp R rows
            (@nat_add middle_left middle_right) (succ columns0)
            (@comm_ring_matrix_horizontal
              R rows middle_left middle_right A B)
            (@comm_ring_matrix_vertical
              R middle_left middle_right (succ columns0) F0 G0))
          (@comm_ring_matrix_add R rows (succ columns0)
            (@comm_ring_matrix_comp R rows middle_left
              (succ columns0) A F0)
            (@comm_ring_matrix_comp R rows middle_right
              (succ columns0) B G0))
          (@comm_ring_matrix_horizontal_apply_path R rows
            middle_left middle_right A B
            (@finite_family_head
              (@CommRingVector R middle_left) columns0 F0)
            (@finite_family_head
              (@CommRingVector R middle_right) columns0 G0))
          (ih
            (@finite_family_tail
              (@CommRingVector R middle_left) columns0 F0)
            (@finite_family_tail
              (@CommRingVector R middle_right) columns0 G0)))
    columns) F G;

// Top row of a diagonal composite has only its left diagonal block.
symbol comm_ring_matrix_block_diag_top_comp_path
  (R : τ CommRing)
  (rows_left middle_left middle_right columns_left columns_right : τ Nat_grpd)
  (A : τ (@CommRingMatrix R rows_left middle_left))
  (B : τ (@CommRingMatrix R middle_left columns_left))
  (E : τ (@CommRingMatrix R middle_right columns_right))
  : τ (@= (@CommRingMatrix R rows_left
      (@nat_add columns_left columns_right))
      (@comm_ring_matrix_comp R rows_left
        (@nat_add middle_left middle_right)
        (@nat_add columns_left columns_right)
        (@comm_ring_matrix_horizontal R rows_left
          middle_left middle_right A
          (@comm_ring_matrix_zero R rows_left middle_right))
        (@comm_ring_matrix_block_diag R
          middle_left middle_right columns_left columns_right B E))
      (@comm_ring_matrix_horizontal R rows_left
        columns_left columns_right
        (@comm_ring_matrix_comp R rows_left middle_left columns_left A B)
        (@comm_ring_matrix_zero R rows_left columns_right)))
≔ @eq_trans
    (@CommRingMatrix R rows_left (@nat_add columns_left columns_right))
    (@comm_ring_matrix_comp R rows_left
      (@nat_add middle_left middle_right)
      (@nat_add columns_left columns_right)
      (@comm_ring_matrix_horizontal R rows_left
        middle_left middle_right A
        (@comm_ring_matrix_zero R rows_left middle_right))
      (@comm_ring_matrix_block_diag R
        middle_left middle_right columns_left columns_right B E))
    (@comm_ring_matrix_add R rows_left
      (@nat_add columns_left columns_right)
      (@comm_ring_matrix_comp R rows_left middle_left
        (@nat_add columns_left columns_right) A
        (@comm_ring_matrix_horizontal R middle_left
          columns_left columns_right B
          (@comm_ring_matrix_zero R middle_left columns_right)))
      (@comm_ring_matrix_comp R rows_left middle_right
        (@nat_add columns_left columns_right)
        (@comm_ring_matrix_zero R rows_left middle_right)
        (@comm_ring_matrix_horizontal R middle_right
          columns_left columns_right
          (@comm_ring_matrix_zero R middle_right columns_left) E)))
    (@comm_ring_matrix_horizontal R rows_left
      columns_left columns_right
      (@comm_ring_matrix_comp R rows_left middle_left columns_left A B)
      (@comm_ring_matrix_zero R rows_left columns_right))
    (@comm_ring_matrix_horizontal_vertical_comp_path
      R rows_left middle_left middle_right
      (@nat_add columns_left columns_right)
      A (@comm_ring_matrix_zero R rows_left middle_right)
      (@comm_ring_matrix_horizontal R middle_left
        columns_left columns_right B
        (@comm_ring_matrix_zero R middle_left columns_right))
      (@comm_ring_matrix_horizontal R middle_right
        columns_left columns_right
        (@comm_ring_matrix_zero R middle_right columns_left) E))
    (@eq_trans
      (@CommRingMatrix R rows_left (@nat_add columns_left columns_right))
      (@comm_ring_matrix_add R rows_left
        (@nat_add columns_left columns_right)
        (@comm_ring_matrix_comp R rows_left middle_left
          (@nat_add columns_left columns_right) A
          (@comm_ring_matrix_horizontal R middle_left
            columns_left columns_right B
            (@comm_ring_matrix_zero R middle_left columns_right)))
        (@comm_ring_matrix_comp R rows_left middle_right
          (@nat_add columns_left columns_right)
          (@comm_ring_matrix_zero R rows_left middle_right)
          (@comm_ring_matrix_horizontal R middle_right
            columns_left columns_right
            (@comm_ring_matrix_zero R middle_right columns_left) E)))
      (@comm_ring_matrix_add R rows_left
        (@nat_add columns_left columns_right)
        (@comm_ring_matrix_horizontal R rows_left
          columns_left columns_right
          (@comm_ring_matrix_comp R rows_left middle_left columns_left A B)
          (@comm_ring_matrix_zero R rows_left columns_right))
        (@comm_ring_matrix_zero R rows_left
          (@nat_add columns_left columns_right)))
      (@comm_ring_matrix_horizontal R rows_left
        columns_left columns_right
        (@comm_ring_matrix_comp R rows_left middle_left columns_left A B)
        (@comm_ring_matrix_zero R rows_left columns_right))
      (@comm_ring_matrix_add_congr_path R rows_left
        (@nat_add columns_left columns_right)
        (@comm_ring_matrix_comp R rows_left middle_left
          (@nat_add columns_left columns_right) A
          (@comm_ring_matrix_horizontal R middle_left
            columns_left columns_right B
            (@comm_ring_matrix_zero R middle_left columns_right)))
        (@comm_ring_matrix_horizontal R rows_left
          columns_left columns_right
          (@comm_ring_matrix_comp R rows_left middle_left columns_left A B)
          (@comm_ring_matrix_zero R rows_left columns_right))
        (@comm_ring_matrix_comp R rows_left middle_right
          (@nat_add columns_left columns_right)
          (@comm_ring_matrix_zero R rows_left middle_right)
          (@comm_ring_matrix_horizontal R middle_right
            columns_left columns_right
            (@comm_ring_matrix_zero R middle_right columns_left) E))
        (@comm_ring_matrix_zero R rows_left
          (@nat_add columns_left columns_right))
        (@eq_trans
          (@CommRingMatrix R rows_left (@nat_add columns_left columns_right))
          (@comm_ring_matrix_comp R rows_left middle_left
            (@nat_add columns_left columns_right) A
            (@comm_ring_matrix_horizontal R middle_left
              columns_left columns_right B
              (@comm_ring_matrix_zero R middle_left columns_right)))
          (@comm_ring_matrix_horizontal R rows_left
            columns_left columns_right
            (@comm_ring_matrix_comp R rows_left middle_left columns_left A B)
            (@comm_ring_matrix_comp R rows_left middle_left columns_right A
              (@comm_ring_matrix_zero R middle_left columns_right)))
          (@comm_ring_matrix_horizontal R rows_left
            columns_left columns_right
            (@comm_ring_matrix_comp R rows_left middle_left columns_left A B)
            (@comm_ring_matrix_zero R rows_left columns_right))
          (@comm_ring_matrix_comp_horizontal_path R rows_left middle_left
            columns_left columns_right A B
            (@comm_ring_matrix_zero R middle_left columns_right))
          (@comm_ring_matrix_horizontal_congr_path R rows_left
            columns_left columns_right
            (@comm_ring_matrix_comp R rows_left middle_left columns_left A B)
            (@comm_ring_matrix_comp R rows_left middle_left columns_left A B)
            (@comm_ring_matrix_comp R rows_left middle_left columns_right A
              (@comm_ring_matrix_zero R middle_left columns_right))
            (@comm_ring_matrix_zero R rows_left columns_right)
            (@eq_refl _ _)
            (@comm_ring_matrix_comp_zero_right_path R rows_left middle_left
              columns_right A)))
        (@comm_ring_matrix_comp_zero_left_path R rows_left middle_right
          (@nat_add columns_left columns_right)
          (@comm_ring_matrix_horizontal R middle_right
            columns_left columns_right
            (@comm_ring_matrix_zero R middle_right columns_left) E)))
      (@comm_ring_matrix_add_zero_right_path R rows_left
        (@nat_add columns_left columns_right)
        (@comm_ring_matrix_horizontal R rows_left
          columns_left columns_right
          (@comm_ring_matrix_comp R rows_left middle_left columns_left A B)
          (@comm_ring_matrix_zero R rows_left columns_right))));

// Bottom row of a diagonal composite has only its right diagonal block.
symbol comm_ring_matrix_block_diag_bottom_comp_path
  (R : τ CommRing)
  (rows_right middle_left middle_right columns_left columns_right : τ Nat_grpd)
  (D : τ (@CommRingMatrix R rows_right middle_right))
  (B : τ (@CommRingMatrix R middle_left columns_left))
  (E : τ (@CommRingMatrix R middle_right columns_right))
  : τ (@= (@CommRingMatrix R rows_right
      (@nat_add columns_left columns_right))
      (@comm_ring_matrix_comp R rows_right
        (@nat_add middle_left middle_right)
        (@nat_add columns_left columns_right)
        (@comm_ring_matrix_horizontal R rows_right
          middle_left middle_right
          (@comm_ring_matrix_zero R rows_right middle_left) D)
        (@comm_ring_matrix_block_diag R
          middle_left middle_right columns_left columns_right B E))
      (@comm_ring_matrix_horizontal R rows_right
        columns_left columns_right
        (@comm_ring_matrix_zero R rows_right columns_left)
        (@comm_ring_matrix_comp R rows_right middle_right columns_right D E)))
≔ @eq_trans
    (@CommRingMatrix R rows_right (@nat_add columns_left columns_right))
    (@comm_ring_matrix_comp R rows_right
      (@nat_add middle_left middle_right)
      (@nat_add columns_left columns_right)
      (@comm_ring_matrix_horizontal R rows_right
        middle_left middle_right
        (@comm_ring_matrix_zero R rows_right middle_left) D)
      (@comm_ring_matrix_block_diag R
        middle_left middle_right columns_left columns_right B E))
    (@comm_ring_matrix_add R rows_right
      (@nat_add columns_left columns_right)
      (@comm_ring_matrix_comp R rows_right middle_left
        (@nat_add columns_left columns_right)
        (@comm_ring_matrix_zero R rows_right middle_left)
        (@comm_ring_matrix_horizontal R middle_left
          columns_left columns_right B
          (@comm_ring_matrix_zero R middle_left columns_right)))
      (@comm_ring_matrix_comp R rows_right middle_right
        (@nat_add columns_left columns_right) D
        (@comm_ring_matrix_horizontal R middle_right
          columns_left columns_right
          (@comm_ring_matrix_zero R middle_right columns_left) E)))
    (@comm_ring_matrix_horizontal R rows_right
      columns_left columns_right
      (@comm_ring_matrix_zero R rows_right columns_left)
      (@comm_ring_matrix_comp R rows_right middle_right columns_right D E))
    (@comm_ring_matrix_horizontal_vertical_comp_path
      R rows_right middle_left middle_right
      (@nat_add columns_left columns_right)
      (@comm_ring_matrix_zero R rows_right middle_left) D
      (@comm_ring_matrix_horizontal R middle_left
        columns_left columns_right B
        (@comm_ring_matrix_zero R middle_left columns_right))
      (@comm_ring_matrix_horizontal R middle_right
        columns_left columns_right
        (@comm_ring_matrix_zero R middle_right columns_left) E))
    (@eq_trans
      (@CommRingMatrix R rows_right (@nat_add columns_left columns_right))
      (@comm_ring_matrix_add R rows_right
        (@nat_add columns_left columns_right)
        (@comm_ring_matrix_comp R rows_right middle_left
          (@nat_add columns_left columns_right)
          (@comm_ring_matrix_zero R rows_right middle_left)
          (@comm_ring_matrix_horizontal R middle_left
            columns_left columns_right B
            (@comm_ring_matrix_zero R middle_left columns_right)))
        (@comm_ring_matrix_comp R rows_right middle_right
          (@nat_add columns_left columns_right) D
          (@comm_ring_matrix_horizontal R middle_right
            columns_left columns_right
            (@comm_ring_matrix_zero R middle_right columns_left) E)))
      (@comm_ring_matrix_add R rows_right
        (@nat_add columns_left columns_right)
        (@comm_ring_matrix_zero R rows_right
          (@nat_add columns_left columns_right))
        (@comm_ring_matrix_horizontal R rows_right
          columns_left columns_right
          (@comm_ring_matrix_zero R rows_right columns_left)
          (@comm_ring_matrix_comp R rows_right middle_right columns_right D E)))
      (@comm_ring_matrix_horizontal R rows_right
        columns_left columns_right
        (@comm_ring_matrix_zero R rows_right columns_left)
        (@comm_ring_matrix_comp R rows_right middle_right columns_right D E))
      (@comm_ring_matrix_add_congr_path R rows_right
        (@nat_add columns_left columns_right)
        (@comm_ring_matrix_comp R rows_right middle_left
          (@nat_add columns_left columns_right)
          (@comm_ring_matrix_zero R rows_right middle_left)
          (@comm_ring_matrix_horizontal R middle_left
            columns_left columns_right B
            (@comm_ring_matrix_zero R middle_left columns_right)))
        (@comm_ring_matrix_zero R rows_right
          (@nat_add columns_left columns_right))
        (@comm_ring_matrix_comp R rows_right middle_right
          (@nat_add columns_left columns_right) D
          (@comm_ring_matrix_horizontal R middle_right
            columns_left columns_right
            (@comm_ring_matrix_zero R middle_right columns_left) E))
        (@comm_ring_matrix_horizontal R rows_right
          columns_left columns_right
          (@comm_ring_matrix_zero R rows_right columns_left)
          (@comm_ring_matrix_comp R rows_right middle_right columns_right D E))
        (@comm_ring_matrix_comp_zero_left_path R rows_right middle_left
          (@nat_add columns_left columns_right)
          (@comm_ring_matrix_horizontal R middle_left
            columns_left columns_right B
            (@comm_ring_matrix_zero R middle_left columns_right)))
        (@eq_trans
          (@CommRingMatrix R rows_right (@nat_add columns_left columns_right))
          (@comm_ring_matrix_comp R rows_right middle_right
            (@nat_add columns_left columns_right) D
            (@comm_ring_matrix_horizontal R middle_right
              columns_left columns_right
              (@comm_ring_matrix_zero R middle_right columns_left) E))
          (@comm_ring_matrix_horizontal R rows_right
            columns_left columns_right
            (@comm_ring_matrix_comp R rows_right middle_right columns_left D
              (@comm_ring_matrix_zero R middle_right columns_left))
            (@comm_ring_matrix_comp R rows_right middle_right columns_right D E))
          (@comm_ring_matrix_horizontal R rows_right
            columns_left columns_right
            (@comm_ring_matrix_zero R rows_right columns_left)
            (@comm_ring_matrix_comp R rows_right middle_right columns_right D E))
          (@comm_ring_matrix_comp_horizontal_path R rows_right middle_right
            columns_left columns_right D
            (@comm_ring_matrix_zero R middle_right columns_left) E)
          (@comm_ring_matrix_horizontal_congr_path R rows_right
            columns_left columns_right
            (@comm_ring_matrix_comp R rows_right middle_right columns_left D
              (@comm_ring_matrix_zero R middle_right columns_left))
            (@comm_ring_matrix_zero R rows_right columns_left)
            (@comm_ring_matrix_comp R rows_right middle_right columns_right D E)
            (@comm_ring_matrix_comp R rows_right middle_right columns_right D E)
            (@comm_ring_matrix_comp_zero_right_path R rows_right middle_right
              columns_left D)
            (@eq_refl _ _))))
      (@comm_ring_matrix_add_zero_left_path R rows_right
        (@nat_add columns_left columns_right)
        (@comm_ring_matrix_horizontal R rows_right
          columns_left columns_right
          (@comm_ring_matrix_zero R rows_right columns_left)
          (@comm_ring_matrix_comp R rows_right middle_right columns_right D E))));

// Block-diagonal matrices compose blockwise.
symbol comm_ring_matrix_block_diag_comp_path
  (R : τ CommRing)
  (rows_left rows_right middle_left middle_right
    columns_left columns_right : τ Nat_grpd)
  (A : τ (@CommRingMatrix R rows_left middle_left))
  (D : τ (@CommRingMatrix R rows_right middle_right))
  (B : τ (@CommRingMatrix R middle_left columns_left))
  (E : τ (@CommRingMatrix R middle_right columns_right))
  : τ (@= (@CommRingMatrix R
      (@nat_add rows_left rows_right)
      (@nat_add columns_left columns_right))
      (@comm_ring_matrix_comp R
        (@nat_add rows_left rows_right)
        (@nat_add middle_left middle_right)
        (@nat_add columns_left columns_right)
        (@comm_ring_matrix_block_diag R
          rows_left rows_right middle_left middle_right A D)
        (@comm_ring_matrix_block_diag R
          middle_left middle_right columns_left columns_right B E))
      (@comm_ring_matrix_block_diag R
        rows_left rows_right columns_left columns_right
        (@comm_ring_matrix_comp R rows_left middle_left columns_left A B)
        (@comm_ring_matrix_comp R rows_right middle_right columns_right D E)))
≔ @eq_trans
    (@CommRingMatrix R
      (@nat_add rows_left rows_right)
      (@nat_add columns_left columns_right))
    (@comm_ring_matrix_comp R
      (@nat_add rows_left rows_right)
      (@nat_add middle_left middle_right)
      (@nat_add columns_left columns_right)
      (@comm_ring_matrix_block_diag R
        rows_left rows_right middle_left middle_right A D)
      (@comm_ring_matrix_block_diag R
        middle_left middle_right columns_left columns_right B E))
    (@comm_ring_matrix_vertical R rows_left rows_right
      (@nat_add columns_left columns_right)
      (@comm_ring_matrix_comp R rows_left
        (@nat_add middle_left middle_right)
        (@nat_add columns_left columns_right)
        (@comm_ring_matrix_horizontal R rows_left
          middle_left middle_right A
          (@comm_ring_matrix_zero R rows_left middle_right))
        (@comm_ring_matrix_block_diag R
          middle_left middle_right columns_left columns_right B E))
      (@comm_ring_matrix_comp R rows_right
        (@nat_add middle_left middle_right)
        (@nat_add columns_left columns_right)
        (@comm_ring_matrix_horizontal R rows_right
          middle_left middle_right
          (@comm_ring_matrix_zero R rows_right middle_left) D)
        (@comm_ring_matrix_block_diag R
          middle_left middle_right columns_left columns_right B E)))
    (@comm_ring_matrix_block_diag R
      rows_left rows_right columns_left columns_right
      (@comm_ring_matrix_comp R rows_left middle_left columns_left A B)
      (@comm_ring_matrix_comp R rows_right middle_right columns_right D E))
    (@comm_ring_matrix_vertical_comp_path R rows_left rows_right
      (@nat_add middle_left middle_right)
      (@nat_add columns_left columns_right)
      (@comm_ring_matrix_horizontal R rows_left
        middle_left middle_right A
        (@comm_ring_matrix_zero R rows_left middle_right))
      (@comm_ring_matrix_horizontal R rows_right
        middle_left middle_right
        (@comm_ring_matrix_zero R rows_right middle_left) D)
      (@comm_ring_matrix_block_diag R
        middle_left middle_right columns_left columns_right B E))
    (@comm_ring_matrix_vertical_congr_path R rows_left rows_right
      (@nat_add columns_left columns_right)
      (@comm_ring_matrix_comp R rows_left
        (@nat_add middle_left middle_right)
        (@nat_add columns_left columns_right)
        (@comm_ring_matrix_horizontal R rows_left
          middle_left middle_right A
          (@comm_ring_matrix_zero R rows_left middle_right))
        (@comm_ring_matrix_block_diag R
          middle_left middle_right columns_left columns_right B E))
      (@comm_ring_matrix_horizontal R rows_left
        columns_left columns_right
        (@comm_ring_matrix_comp R rows_left middle_left columns_left A B)
        (@comm_ring_matrix_zero R rows_left columns_right))
      (@comm_ring_matrix_comp R rows_right
        (@nat_add middle_left middle_right)
        (@nat_add columns_left columns_right)
        (@comm_ring_matrix_horizontal R rows_right
          middle_left middle_right
          (@comm_ring_matrix_zero R rows_right middle_left) D)
        (@comm_ring_matrix_block_diag R
          middle_left middle_right columns_left columns_right B E))
      (@comm_ring_matrix_horizontal R rows_right
        columns_left columns_right
        (@comm_ring_matrix_zero R rows_right columns_left)
        (@comm_ring_matrix_comp R rows_right middle_right columns_right D E))
      (@comm_ring_matrix_block_diag_top_comp_path R rows_left
        middle_left middle_right columns_left columns_right A B E)
      (@comm_ring_matrix_block_diag_bottom_comp_path R rows_right
        middle_left middle_right columns_left columns_right D B E));

// The diagonal of two identity matrices is the identity at the rank sum.
symbol comm_ring_matrix_block_diag_id_path
  (R : τ CommRing)
  (m n : τ Nat_grpd)
  : τ (@= (@CommRingMatrix R (@nat_add m n) (@nat_add m n))
      (@comm_ring_matrix_block_diag R m n m n
        (@comm_ring_finite_free_id_matrix R m)
        (@comm_ring_finite_free_id_matrix R n))
      (@comm_ring_finite_free_id_matrix R (@nat_add m n)))
≔ @eq_trans
    (@CommRingMatrix R (@nat_add m n) (@nat_add m n))
    (@comm_ring_matrix_block_diag R m n m n
      (@comm_ring_finite_free_id_matrix R m)
      (@comm_ring_finite_free_id_matrix R n))
    (@comm_ring_matrix_vertical R m n (@nat_add m n)
      (@comm_ring_matrix_comp R m (@nat_add m n) (@nat_add m n)
        (@comm_ring_matrix_proj1 R m n)
        (@comm_ring_finite_free_id_matrix R (@nat_add m n)))
      (@comm_ring_matrix_comp R n (@nat_add m n) (@nat_add m n)
        (@comm_ring_matrix_proj2 R m n)
        (@comm_ring_finite_free_id_matrix R (@nat_add m n))))
    (@comm_ring_finite_free_id_matrix R (@nat_add m n))
    (@comm_ring_matrix_vertical_congr_path R m n (@nat_add m n)
      (@comm_ring_matrix_proj1 R m n)
      (@comm_ring_matrix_comp R m (@nat_add m n) (@nat_add m n)
        (@comm_ring_matrix_proj1 R m n)
        (@comm_ring_finite_free_id_matrix R (@nat_add m n)))
      (@comm_ring_matrix_proj2 R m n)
      (@comm_ring_matrix_comp R n (@nat_add m n) (@nat_add m n)
        (@comm_ring_matrix_proj2 R m n)
        (@comm_ring_finite_free_id_matrix R (@nat_add m n)))
      (@eq_sym
        (@CommRingMatrix R m (@nat_add m n))
        (@comm_ring_matrix_comp R m (@nat_add m n) (@nat_add m n)
          (@comm_ring_matrix_proj1 R m n)
          (@comm_ring_finite_free_id_matrix R (@nat_add m n)))
        (@comm_ring_matrix_proj1 R m n)
        (@comm_ring_matrix_comp_right_identity_path R
          (@nat_add m n) m (@comm_ring_matrix_proj1 R m n)))
      (@eq_sym
        (@CommRingMatrix R n (@nat_add m n))
        (@comm_ring_matrix_comp R n (@nat_add m n) (@nat_add m n)
          (@comm_ring_matrix_proj2 R m n)
          (@comm_ring_finite_free_id_matrix R (@nat_add m n)))
        (@comm_ring_matrix_proj2 R m n)
        (@comm_ring_matrix_comp_right_identity_path R
          (@nat_add m n) n (@comm_ring_matrix_proj2 R m n))))
    (@comm_ring_matrix_vertical_proj_eta_path R m n (@nat_add m n)
      (@comm_ring_finite_free_id_matrix R (@nat_add m n)));
