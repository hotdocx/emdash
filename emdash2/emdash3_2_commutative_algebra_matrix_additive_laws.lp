/*
  Additive and bilinear laws for finite free vectors and column matrices.

  All paths are constructed by Nat recursion over the existing nested-Sigma
  finite-family representation. The module derives vector additive/scalar
  laws, matrix-action linearity, matrix additive-group laws, zero composition,
  and both distributivity orientations. It introduces no rewrite or
  unification rule and no opaque algebraic witness.
*/

require open emdash.emdash3_2_commutative_algebra_derived_laws;
require open emdash.emdash3_2_commutative_algebra_presentation_operations;

symbol finite_family_succ_path
  [A : Grpd]
  [n : τ Nat_grpd]
  (xs ys : τ (@FiniteFamily A (succ n)))
  (head_path : τ (@= A
      (@finite_family_head A n xs)
      (@finite_family_head A n ys)))
  (tail_path : τ (@= (@FiniteFamily A n)
      (@finite_family_tail A n xs)
      (@finite_family_tail A n ys)))
  : τ (@= (@FiniteFamily A (succ n)) xs ys)
≔ @Struct_sigma
    (@= A
      (@finite_family_head A n xs)
      (@finite_family_head A n ys))
    (λ p : τ (@= A
        (@finite_family_head A n xs)
        (@finite_family_head A n ys)),
      @PathOver A
        (λ _ : τ A, @FiniteFamily A n)
        (@finite_family_head A n xs)
        (@finite_family_head A n ys)
        p
        (@finite_family_tail A n xs)
        (@finite_family_tail A n ys))
    head_path
    (@const_pathover
      A (@FiniteFamily A n)
      (@finite_family_head A n xs)
      (@finite_family_head A n ys)
      (@finite_family_tail A n xs)
      (@finite_family_tail A n ys)
      head_path tail_path);

symbol comm_ring_vector_add_zero_right_path
  (R : τ CommRing)
  (n : τ Nat_grpd)
  (u : τ (@CommRingVector R n))
  : τ (@= (@CommRingVector R n)
      (@comm_ring_vector_add R n u (@comm_ring_vector_zero R n))
      u)
≔ (@nat_elim
    (λ n0 : τ Nat_grpd,
      @Pi_grpd (@CommRingVector R n0)
        (λ u0 : τ (@CommRingVector R n0),
          @= (@CommRingVector R n0)
            (@comm_ring_vector_add R n0 u0
              (@comm_ring_vector_zero R n0))
            u0))
    (λ u0 : τ (@CommRingVector R zero),
      (sigma_Snd unit_is_contr) u0)
    (λ n0 : τ Nat_grpd,
      λ ih : τ (@Pi_grpd (@CommRingVector R n0)
        (λ u0 : τ (@CommRingVector R n0),
          @= (@CommRingVector R n0)
            (@comm_ring_vector_add R n0 u0
              (@comm_ring_vector_zero R n0))
            u0)),
      λ u0 : τ (@CommRingVector R (succ n0)),
        @finite_family_succ_path
          (@comm_ring_carrier R) n0
          (@comm_ring_vector_add R (succ n0) u0
            (@comm_ring_vector_zero R (succ n0)))
          u0
          ((@comm_ring_add_zero_law R)
            (@finite_family_head (@comm_ring_carrier R) n0 u0))
          (ih (@finite_family_tail (@comm_ring_carrier R) n0 u0)))
    n) u;

symbol comm_ring_vector_add_zero_left_path
  (R : τ CommRing)
  (n : τ Nat_grpd)
  (u : τ (@CommRingVector R n))
  : τ (@= (@CommRingVector R n)
      (@comm_ring_vector_add R n (@comm_ring_vector_zero R n) u)
      u)
≔ (@nat_elim
    (λ n0 : τ Nat_grpd,
      @Pi_grpd (@CommRingVector R n0)
        (λ u0 : τ (@CommRingVector R n0),
          @= (@CommRingVector R n0)
            (@comm_ring_vector_add R n0
              (@comm_ring_vector_zero R n0) u0)
            u0))
    (λ u0 : τ (@CommRingVector R zero),
      (sigma_Snd unit_is_contr) u0)
    (λ n0 : τ Nat_grpd,
      λ ih : τ (@Pi_grpd (@CommRingVector R n0)
        (λ u0 : τ (@CommRingVector R n0),
          @= (@CommRingVector R n0)
            (@comm_ring_vector_add R n0
              (@comm_ring_vector_zero R n0) u0)
            u0)),
      λ u0 : τ (@CommRingVector R (succ n0)),
        @finite_family_succ_path
          (@comm_ring_carrier R) n0
          (@comm_ring_vector_add R (succ n0)
            (@comm_ring_vector_zero R (succ n0)) u0)
          u0
          (@comm_ring_add_zero_left_path R
            (@finite_family_head (@comm_ring_carrier R) n0 u0))
          (ih (@finite_family_tail (@comm_ring_carrier R) n0 u0)))
    n) u;

symbol comm_ring_vector_add_assoc_path
  (R : τ CommRing)
  (n : τ Nat_grpd)
  (u v w : τ (@CommRingVector R n))
  : τ (@= (@CommRingVector R n)
      (@comm_ring_vector_add R n
        (@comm_ring_vector_add R n u v) w)
      (@comm_ring_vector_add R n u
        (@comm_ring_vector_add R n v w)))
≔ (@nat_elim
    (λ n0 : τ Nat_grpd,
      @Pi_grpd (@CommRingVector R n0) (λ u0 : τ _,
        @Pi_grpd (@CommRingVector R n0) (λ v0 : τ _,
          @Pi_grpd (@CommRingVector R n0) (λ w0 : τ _,
            @= (@CommRingVector R n0)
              (@comm_ring_vector_add R n0
                (@comm_ring_vector_add R n0 u0 v0) w0)
              (@comm_ring_vector_add R n0 u0
                (@comm_ring_vector_add R n0 v0 w0))))))
    (λ _ : τ _, λ _ : τ _, λ _ : τ _, @eq_refl Unit_grpd tt)
    (λ n0 : τ Nat_grpd, λ ih : τ _,
      λ u0 : τ _, λ v0 : τ _, λ w0 : τ _,
        @finite_family_succ_path
          (@comm_ring_carrier R) n0
          (@comm_ring_vector_add R (succ n0)
            (@comm_ring_vector_add R (succ n0) u0 v0) w0)
          (@comm_ring_vector_add R (succ n0) u0
            (@comm_ring_vector_add R (succ n0) v0 w0))
          ((@comm_ring_add_assoc_law R)
            (@finite_family_head (@comm_ring_carrier R) n0 u0)
            (@finite_family_head (@comm_ring_carrier R) n0 v0)
            (@finite_family_head (@comm_ring_carrier R) n0 w0))
          (ih
            (@finite_family_tail (@comm_ring_carrier R) n0 u0)
            (@finite_family_tail (@comm_ring_carrier R) n0 v0)
            (@finite_family_tail (@comm_ring_carrier R) n0 w0)))
    n) u v w;

symbol comm_ring_vector_add_comm_path
  (R : τ CommRing)
  (n : τ Nat_grpd)
  (u v : τ (@CommRingVector R n))
  : τ (@= (@CommRingVector R n)
      (@comm_ring_vector_add R n u v)
      (@comm_ring_vector_add R n v u))
≔ (@nat_elim
    (λ n0 : τ Nat_grpd,
      @Pi_grpd (@CommRingVector R n0) (λ u0 : τ _,
        @Pi_grpd (@CommRingVector R n0) (λ v0 : τ _,
          @= (@CommRingVector R n0)
            (@comm_ring_vector_add R n0 u0 v0)
            (@comm_ring_vector_add R n0 v0 u0))))
    (λ _ : τ _, λ _ : τ _, @eq_refl Unit_grpd tt)
    (λ n0 : τ Nat_grpd, λ ih : τ _,
      λ u0 : τ _, λ v0 : τ _,
        @finite_family_succ_path
          (@comm_ring_carrier R) n0
          (@comm_ring_vector_add R (succ n0) u0 v0)
          (@comm_ring_vector_add R (succ n0) v0 u0)
          ((@comm_ring_add_comm_law R)
            (@finite_family_head (@comm_ring_carrier R) n0 u0)
            (@finite_family_head (@comm_ring_carrier R) n0 v0))
          (ih
            (@finite_family_tail (@comm_ring_carrier R) n0 u0)
            (@finite_family_tail (@comm_ring_carrier R) n0 v0)))
    n) u v;

symbol comm_ring_vector_add_inv_path
  (R : τ CommRing)
  (n : τ Nat_grpd)
  (u : τ (@CommRingVector R n))
  : τ (@= (@CommRingVector R n)
      (@comm_ring_vector_add R n u (@comm_ring_vector_neg R n u))
      (@comm_ring_vector_zero R n))
≔ (@nat_elim
    (λ n0 : τ Nat_grpd,
      @Pi_grpd (@CommRingVector R n0) (λ u0 : τ _,
        @= (@CommRingVector R n0)
          (@comm_ring_vector_add R n0 u0
            (@comm_ring_vector_neg R n0 u0))
          (@comm_ring_vector_zero R n0)))
    (λ _ : τ _, @eq_refl Unit_grpd tt)
    (λ n0 : τ Nat_grpd, λ ih : τ _, λ u0 : τ _,
      @finite_family_succ_path
        (@comm_ring_carrier R) n0
        (@comm_ring_vector_add R (succ n0) u0
          (@comm_ring_vector_neg R (succ n0) u0))
        (@comm_ring_vector_zero R (succ n0))
        ((@comm_ring_add_inv_law R)
          (@finite_family_head (@comm_ring_carrier R) n0 u0))
        (ih (@finite_family_tail (@comm_ring_carrier R) n0 u0)))
    n) u;

symbol comm_ring_vector_scale_zero_scalar_path
  (R : τ CommRing)
  (n : τ Nat_grpd)
  (u : τ (@CommRingVector R n))
  : τ (@= (@CommRingVector R n)
      (@comm_ring_vector_scale R n (@comm_ring_zero R) u)
      (@comm_ring_vector_zero R n))
≔ (@nat_elim
    (λ n0 : τ Nat_grpd,
      @Pi_grpd (@CommRingVector R n0) (λ u0 : τ _,
        @= (@CommRingVector R n0)
          (@comm_ring_vector_scale R n0 (@comm_ring_zero R) u0)
          (@comm_ring_vector_zero R n0)))
    (λ _ : τ _, @eq_refl Unit_grpd tt)
    (λ n0 : τ Nat_grpd, λ ih : τ _, λ u0 : τ _,
      @finite_family_succ_path
        (@comm_ring_carrier R) n0
        (@comm_ring_vector_scale R (succ n0) (@comm_ring_zero R) u0)
        (@comm_ring_vector_zero R (succ n0))
        (@comm_ring_mul_zero_left_path R
          (@finite_family_head (@comm_ring_carrier R) n0 u0))
        (ih (@finite_family_tail (@comm_ring_carrier R) n0 u0)))
    n) u;

symbol comm_ring_vector_scale_zero_vector_path
  (R : τ CommRing)
  (n : τ Nat_grpd)
  (a : τ (@comm_ring_carrier R))
  : τ (@= (@CommRingVector R n)
      (@comm_ring_vector_scale R n a (@comm_ring_vector_zero R n))
      (@comm_ring_vector_zero R n))
≔ @nat_elim
    (λ n0 : τ Nat_grpd,
      @= (@CommRingVector R n0)
        (@comm_ring_vector_scale R n0 a (@comm_ring_vector_zero R n0))
        (@comm_ring_vector_zero R n0))
    (@eq_refl Unit_grpd tt)
    (λ n0 : τ Nat_grpd, λ ih : τ _,
      @finite_family_succ_path
        (@comm_ring_carrier R) n0
        (@comm_ring_vector_scale R (succ n0) a
          (@comm_ring_vector_zero R (succ n0)))
        (@comm_ring_vector_zero R (succ n0))
        (@comm_ring_mul_zero_right_path R a)
        ih)
    n;

symbol comm_ring_vector_scale_add_vector_path
  (R : τ CommRing)
  (n : τ Nat_grpd)
  (a : τ (@comm_ring_carrier R))
  (u v : τ (@CommRingVector R n))
  : τ (@= (@CommRingVector R n)
      (@comm_ring_vector_scale R n a (@comm_ring_vector_add R n u v))
      (@comm_ring_vector_add R n
        (@comm_ring_vector_scale R n a u)
        (@comm_ring_vector_scale R n a v)))
≔ (@nat_elim
    (λ n0 : τ Nat_grpd,
      @Pi_grpd (@CommRingVector R n0) (λ u0 : τ _,
        @Pi_grpd (@CommRingVector R n0) (λ v0 : τ _,
          @= (@CommRingVector R n0)
            (@comm_ring_vector_scale R n0 a
              (@comm_ring_vector_add R n0 u0 v0))
            (@comm_ring_vector_add R n0
              (@comm_ring_vector_scale R n0 a u0)
              (@comm_ring_vector_scale R n0 a v0)))))
    (λ _ : τ _, λ _ : τ _, @eq_refl Unit_grpd tt)
    (λ n0 : τ Nat_grpd, λ ih : τ _, λ u0 : τ _, λ v0 : τ _,
      @finite_family_succ_path
        (@comm_ring_carrier R) n0
        (@comm_ring_vector_scale R (succ n0) a
          (@comm_ring_vector_add R (succ n0) u0 v0))
        (@comm_ring_vector_add R (succ n0)
          (@comm_ring_vector_scale R (succ n0) a u0)
          (@comm_ring_vector_scale R (succ n0) a v0))
        ((@comm_ring_left_distrib_law R) a
          (@finite_family_head (@comm_ring_carrier R) n0 u0)
          (@finite_family_head (@comm_ring_carrier R) n0 v0))
        (ih
          (@finite_family_tail (@comm_ring_carrier R) n0 u0)
          (@finite_family_tail (@comm_ring_carrier R) n0 v0)))
    n) u v;

symbol comm_ring_vector_scale_add_scalar_path
  (R : τ CommRing)
  (n : τ Nat_grpd)
  (a b : τ (@comm_ring_carrier R))
  (u : τ (@CommRingVector R n))
  : τ (@= (@CommRingVector R n)
      (@comm_ring_vector_scale R n (@comm_ring_add R a b) u)
      (@comm_ring_vector_add R n
        (@comm_ring_vector_scale R n a u)
        (@comm_ring_vector_scale R n b u)))
≔ (@nat_elim
    (λ n0 : τ Nat_grpd,
      @Pi_grpd (@CommRingVector R n0) (λ u0 : τ _,
        @= (@CommRingVector R n0)
          (@comm_ring_vector_scale R n0 (@comm_ring_add R a b) u0)
          (@comm_ring_vector_add R n0
            (@comm_ring_vector_scale R n0 a u0)
            (@comm_ring_vector_scale R n0 b u0))))
    (λ _ : τ _, @eq_refl Unit_grpd tt)
    (λ n0 : τ Nat_grpd, λ ih : τ _, λ u0 : τ _,
      @finite_family_succ_path
        (@comm_ring_carrier R) n0
        (@comm_ring_vector_scale R (succ n0) (@comm_ring_add R a b) u0)
        (@comm_ring_vector_add R (succ n0)
          (@comm_ring_vector_scale R (succ n0) a u0)
          (@comm_ring_vector_scale R (succ n0) b u0))
        (@comm_ring_right_distrib_path R a b
          (@finite_family_head (@comm_ring_carrier R) n0 u0))
        (ih (@finite_family_tail (@comm_ring_carrier R) n0 u0)))
    n) u;

symbol comm_ring_vector_add_congr_path
  (R : τ CommRing)
  (n : τ Nat_grpd)
  (u u' v v' : τ (@CommRingVector R n))
  (p : τ (@= (@CommRingVector R n) u u'))
  (q : τ (@= (@CommRingVector R n) v v'))
  : τ (@= (@CommRingVector R n)
      (@comm_ring_vector_add R n u v)
      (@comm_ring_vector_add R n u' v'))
≔ @eq_trans
    (@CommRingVector R n)
    (@comm_ring_vector_add R n u v)
    (@comm_ring_vector_add R n u' v)
    (@comm_ring_vector_add R n u' v')
    (@eq_ap
      (@CommRingVector R n)
      (@CommRingVector R n)
      (λ z : τ (@CommRingVector R n),
        @comm_ring_vector_add R n z v)
      u u' p)
    (@eq_ap
      (@CommRingVector R n)
      (@CommRingVector R n)
      (λ z : τ (@CommRingVector R n),
        @comm_ring_vector_add R n u' z)
      v v' q);

symbol comm_ring_vector_add_interchange_path
  (R : τ CommRing)
  (n : τ Nat_grpd)
  (a b c d : τ (@CommRingVector R n))
  : τ (@= (@CommRingVector R n)
      (@comm_ring_vector_add R n
        (@comm_ring_vector_add R n a b)
        (@comm_ring_vector_add R n c d))
      (@comm_ring_vector_add R n
        (@comm_ring_vector_add R n a c)
        (@comm_ring_vector_add R n b d)))
≔ @eq_trans
    (@CommRingVector R n)
    (@comm_ring_vector_add R n
      (@comm_ring_vector_add R n a b)
      (@comm_ring_vector_add R n c d))
    (@comm_ring_vector_add R n a
      (@comm_ring_vector_add R n b
        (@comm_ring_vector_add R n c d)))
    (@comm_ring_vector_add R n
      (@comm_ring_vector_add R n a c)
      (@comm_ring_vector_add R n b d))
    (@comm_ring_vector_add_assoc_path R n
      a b (@comm_ring_vector_add R n c d))
    (@eq_trans
      (@CommRingVector R n)
      (@comm_ring_vector_add R n a
        (@comm_ring_vector_add R n b
          (@comm_ring_vector_add R n c d)))
      (@comm_ring_vector_add R n a
        (@comm_ring_vector_add R n
          (@comm_ring_vector_add R n b c) d))
      (@comm_ring_vector_add R n
        (@comm_ring_vector_add R n a c)
        (@comm_ring_vector_add R n b d))
      (@eq_ap
        (@CommRingVector R n)
        (@CommRingVector R n)
        (λ z : τ (@CommRingVector R n),
          @comm_ring_vector_add R n a z)
        (@comm_ring_vector_add R n b
          (@comm_ring_vector_add R n c d))
        (@comm_ring_vector_add R n
          (@comm_ring_vector_add R n b c) d)
        (@eq_sym
          (@CommRingVector R n)
          (@comm_ring_vector_add R n
            (@comm_ring_vector_add R n b c) d)
          (@comm_ring_vector_add R n b
            (@comm_ring_vector_add R n c d))
          (@comm_ring_vector_add_assoc_path R n b c d)))
      (@eq_trans
        (@CommRingVector R n)
        (@comm_ring_vector_add R n a
          (@comm_ring_vector_add R n
            (@comm_ring_vector_add R n b c) d))
        (@comm_ring_vector_add R n a
          (@comm_ring_vector_add R n
            (@comm_ring_vector_add R n c b) d))
        (@comm_ring_vector_add R n
          (@comm_ring_vector_add R n a c)
          (@comm_ring_vector_add R n b d))
        (@eq_ap
          (@CommRingVector R n)
          (@CommRingVector R n)
          (λ z : τ (@CommRingVector R n),
            @comm_ring_vector_add R n a
              (@comm_ring_vector_add R n z d))
          (@comm_ring_vector_add R n b c)
          (@comm_ring_vector_add R n c b)
          (@comm_ring_vector_add_comm_path R n b c))
        (@eq_trans
          (@CommRingVector R n)
          (@comm_ring_vector_add R n a
            (@comm_ring_vector_add R n
              (@comm_ring_vector_add R n c b) d))
          (@comm_ring_vector_add R n a
            (@comm_ring_vector_add R n c
              (@comm_ring_vector_add R n b d)))
          (@comm_ring_vector_add R n
            (@comm_ring_vector_add R n a c)
            (@comm_ring_vector_add R n b d))
          (@eq_ap
            (@CommRingVector R n)
            (@CommRingVector R n)
            (λ z : τ (@CommRingVector R n),
              @comm_ring_vector_add R n a z)
            (@comm_ring_vector_add R n
              (@comm_ring_vector_add R n c b) d)
            (@comm_ring_vector_add R n c
              (@comm_ring_vector_add R n b d))
            (@comm_ring_vector_add_assoc_path R n c b d))
          (@eq_sym
            (@CommRingVector R n)
            (@comm_ring_vector_add R n
              (@comm_ring_vector_add R n a c)
              (@comm_ring_vector_add R n b d))
            (@comm_ring_vector_add R n a
              (@comm_ring_vector_add R n c
                (@comm_ring_vector_add R n b d)))
            (@comm_ring_vector_add_assoc_path R n
              a c (@comm_ring_vector_add R n b d))))));

symbol comm_ring_matrix_apply_zero_vector_path
  (R : τ CommRing)
  (rows columns : τ Nat_grpd)
  (A : τ (@CommRingMatrix R rows columns))
  : τ (@= (@CommRingVector R rows)
      (@comm_ring_matrix_apply R rows columns A
        (@comm_ring_vector_zero R columns))
      (@comm_ring_vector_zero R rows))
≔ (@nat_elim
    (λ columns0 : τ Nat_grpd,
      @Pi_grpd (@CommRingMatrix R rows columns0) (λ A0 : τ _,
        @= (@CommRingVector R rows)
          (@comm_ring_matrix_apply R rows columns0 A0
            (@comm_ring_vector_zero R columns0))
          (@comm_ring_vector_zero R rows)))
    (λ _ : τ _, @eq_refl (@CommRingVector R rows)
      (@comm_ring_vector_zero R rows))
    (λ columns0 : τ Nat_grpd, λ ih : τ _, λ A0 : τ _,
      @eq_trans
        (@CommRingVector R rows)
        (@comm_ring_matrix_apply R rows (succ columns0) A0
          (@comm_ring_vector_zero R (succ columns0)))
        (@comm_ring_vector_add R rows
          (@comm_ring_vector_zero R rows)
          (@comm_ring_vector_zero R rows))
        (@comm_ring_vector_zero R rows)
        (@comm_ring_vector_add_congr_path R rows
          (@comm_ring_vector_scale R rows (@comm_ring_zero R)
            (@finite_family_head (@CommRingVector R rows) columns0 A0))
          (@comm_ring_vector_zero R rows)
          (@comm_ring_matrix_apply R rows columns0
            (@finite_family_tail (@CommRingVector R rows) columns0 A0)
            (@comm_ring_vector_zero R columns0))
          (@comm_ring_vector_zero R rows)
          (@comm_ring_vector_scale_zero_scalar_path R rows
            (@finite_family_head (@CommRingVector R rows) columns0 A0))
          (ih (@finite_family_tail (@CommRingVector R rows) columns0 A0)))
        (@comm_ring_vector_add_zero_right_path R rows
          (@comm_ring_vector_zero R rows)))
    columns) A;

symbol comm_ring_matrix_apply_zero_matrix_path
  (R : τ CommRing)
  (rows columns : τ Nat_grpd)
  (x : τ (@CommRingVector R columns))
  : τ (@= (@CommRingVector R rows)
      (@comm_ring_matrix_apply R rows columns
        (@comm_ring_matrix_zero R rows columns) x)
      (@comm_ring_vector_zero R rows))
≔ (@nat_elim
    (λ columns0 : τ Nat_grpd,
      @Pi_grpd (@CommRingVector R columns0) (λ x0 : τ _,
        @= (@CommRingVector R rows)
          (@comm_ring_matrix_apply R rows columns0
            (@comm_ring_matrix_zero R rows columns0) x0)
          (@comm_ring_vector_zero R rows)))
    (λ _ : τ _, @eq_refl (@CommRingVector R rows)
      (@comm_ring_vector_zero R rows))
    (λ columns0 : τ Nat_grpd, λ ih : τ _, λ x0 : τ _,
      @eq_trans
        (@CommRingVector R rows)
        (@comm_ring_matrix_apply R rows (succ columns0)
          (@comm_ring_matrix_zero R rows (succ columns0)) x0)
        (@comm_ring_vector_add R rows
          (@comm_ring_vector_zero R rows)
          (@comm_ring_vector_zero R rows))
        (@comm_ring_vector_zero R rows)
        (@comm_ring_vector_add_congr_path R rows
          (@comm_ring_vector_scale R rows
            (@finite_family_head (@comm_ring_carrier R) columns0 x0)
            (@comm_ring_vector_zero R rows))
          (@comm_ring_vector_zero R rows)
          (@comm_ring_matrix_apply R rows columns0
            (@comm_ring_matrix_zero R rows columns0)
            (@finite_family_tail (@comm_ring_carrier R) columns0 x0))
          (@comm_ring_vector_zero R rows)
          (@comm_ring_vector_scale_zero_vector_path R rows
            (@finite_family_head (@comm_ring_carrier R) columns0 x0))
          (ih (@finite_family_tail (@comm_ring_carrier R) columns0 x0)))
        (@comm_ring_vector_add_zero_right_path R rows
          (@comm_ring_vector_zero R rows)))
    columns) x;

symbol comm_ring_matrix_apply_add_vector_path
  (R : τ CommRing)
  (rows columns : τ Nat_grpd)
  (A : τ (@CommRingMatrix R rows columns))
  (x y : τ (@CommRingVector R columns))
  : τ (@= (@CommRingVector R rows)
      (@comm_ring_matrix_apply R rows columns A
        (@comm_ring_vector_add R columns x y))
      (@comm_ring_vector_add R rows
        (@comm_ring_matrix_apply R rows columns A x)
        (@comm_ring_matrix_apply R rows columns A y)))
≔ (@nat_elim
    (λ columns0 : τ Nat_grpd,
      @Pi_grpd (@CommRingMatrix R rows columns0) (λ A0 : τ _,
        @Pi_grpd (@CommRingVector R columns0) (λ x0 : τ _,
          @Pi_grpd (@CommRingVector R columns0) (λ y0 : τ _,
            @= (@CommRingVector R rows)
              (@comm_ring_matrix_apply R rows columns0 A0
                (@comm_ring_vector_add R columns0 x0 y0))
              (@comm_ring_vector_add R rows
                (@comm_ring_matrix_apply R rows columns0 A0 x0)
                (@comm_ring_matrix_apply R rows columns0 A0 y0))))))
    (λ _ : τ _, λ _ : τ _, λ _ : τ _,
      @eq_sym (@CommRingVector R rows)
        (@comm_ring_vector_add R rows
          (@comm_ring_vector_zero R rows)
          (@comm_ring_vector_zero R rows))
        (@comm_ring_vector_zero R rows)
        (@comm_ring_vector_add_zero_right_path R rows
          (@comm_ring_vector_zero R rows)))
    (λ columns0 : τ Nat_grpd, λ ih : τ _,
      λ A0 : τ _, λ x0 : τ _, λ y0 : τ _,
      @eq_trans
        (@CommRingVector R rows)
        (@comm_ring_matrix_apply R rows (succ columns0) A0
          (@comm_ring_vector_add R (succ columns0) x0 y0))
        (@comm_ring_vector_add R rows
          (@comm_ring_vector_add R rows
            (@comm_ring_vector_scale R rows
              (@finite_family_head (@comm_ring_carrier R) columns0 x0)
              (@finite_family_head (@CommRingVector R rows) columns0 A0))
            (@comm_ring_vector_scale R rows
              (@finite_family_head (@comm_ring_carrier R) columns0 y0)
              (@finite_family_head (@CommRingVector R rows) columns0 A0)))
          (@comm_ring_vector_add R rows
            (@comm_ring_matrix_apply R rows columns0
              (@finite_family_tail (@CommRingVector R rows) columns0 A0)
              (@finite_family_tail (@comm_ring_carrier R) columns0 x0))
            (@comm_ring_matrix_apply R rows columns0
              (@finite_family_tail (@CommRingVector R rows) columns0 A0)
              (@finite_family_tail (@comm_ring_carrier R) columns0 y0))))
        (@comm_ring_vector_add R rows
          (@comm_ring_matrix_apply R rows (succ columns0) A0 x0)
          (@comm_ring_matrix_apply R rows (succ columns0) A0 y0))
        (@comm_ring_vector_add_congr_path R rows
          _ _ _ _
          (@comm_ring_vector_scale_add_scalar_path R rows
            (@finite_family_head (@comm_ring_carrier R) columns0 x0)
            (@finite_family_head (@comm_ring_carrier R) columns0 y0)
            (@finite_family_head (@CommRingVector R rows) columns0 A0))
          (ih
            (@finite_family_tail (@CommRingVector R rows) columns0 A0)
            (@finite_family_tail (@comm_ring_carrier R) columns0 x0)
            (@finite_family_tail (@comm_ring_carrier R) columns0 y0)))
        (@comm_ring_vector_add_interchange_path R rows
          (@comm_ring_vector_scale R rows
            (@finite_family_head (@comm_ring_carrier R) columns0 x0)
            (@finite_family_head (@CommRingVector R rows) columns0 A0))
          (@comm_ring_vector_scale R rows
            (@finite_family_head (@comm_ring_carrier R) columns0 y0)
            (@finite_family_head (@CommRingVector R rows) columns0 A0))
          (@comm_ring_matrix_apply R rows columns0
            (@finite_family_tail (@CommRingVector R rows) columns0 A0)
            (@finite_family_tail (@comm_ring_carrier R) columns0 x0))
          (@comm_ring_matrix_apply R rows columns0
            (@finite_family_tail (@CommRingVector R rows) columns0 A0)
            (@finite_family_tail (@comm_ring_carrier R) columns0 y0))))
    columns) A x y;

symbol comm_ring_matrix_apply_add_matrix_path
  (R : τ CommRing)
  (rows columns : τ Nat_grpd)
  (A B : τ (@CommRingMatrix R rows columns))
  (x : τ (@CommRingVector R columns))
  : τ (@= (@CommRingVector R rows)
      (@comm_ring_matrix_apply R rows columns
        (@comm_ring_matrix_add R rows columns A B) x)
      (@comm_ring_vector_add R rows
        (@comm_ring_matrix_apply R rows columns A x)
        (@comm_ring_matrix_apply R rows columns B x)))
≔ (@nat_elim
    (λ columns0 : τ Nat_grpd,
      @Pi_grpd (@CommRingMatrix R rows columns0) (λ A0 : τ _,
        @Pi_grpd (@CommRingMatrix R rows columns0) (λ B0 : τ _,
          @Pi_grpd (@CommRingVector R columns0) (λ x0 : τ _,
            @= (@CommRingVector R rows)
              (@comm_ring_matrix_apply R rows columns0
                (@comm_ring_matrix_add R rows columns0 A0 B0) x0)
              (@comm_ring_vector_add R rows
                (@comm_ring_matrix_apply R rows columns0 A0 x0)
                (@comm_ring_matrix_apply R rows columns0 B0 x0))))))
    (λ _ : τ _, λ _ : τ _, λ _ : τ _,
      @eq_sym (@CommRingVector R rows)
        (@comm_ring_vector_add R rows
          (@comm_ring_vector_zero R rows)
          (@comm_ring_vector_zero R rows))
        (@comm_ring_vector_zero R rows)
        (@comm_ring_vector_add_zero_right_path R rows
          (@comm_ring_vector_zero R rows)))
    (λ columns0 : τ Nat_grpd, λ ih : τ _,
      λ A0 : τ _, λ B0 : τ _, λ x0 : τ _,
      @eq_trans
        (@CommRingVector R rows)
        (@comm_ring_matrix_apply R rows (succ columns0)
          (@comm_ring_matrix_add R rows (succ columns0) A0 B0) x0)
        (@comm_ring_vector_add R rows
          (@comm_ring_vector_add R rows
            (@comm_ring_vector_scale R rows
              (@finite_family_head (@comm_ring_carrier R) columns0 x0)
              (@finite_family_head (@CommRingVector R rows) columns0 A0))
            (@comm_ring_vector_scale R rows
              (@finite_family_head (@comm_ring_carrier R) columns0 x0)
              (@finite_family_head (@CommRingVector R rows) columns0 B0)))
          (@comm_ring_vector_add R rows
            (@comm_ring_matrix_apply R rows columns0
              (@finite_family_tail (@CommRingVector R rows) columns0 A0)
              (@finite_family_tail (@comm_ring_carrier R) columns0 x0))
            (@comm_ring_matrix_apply R rows columns0
              (@finite_family_tail (@CommRingVector R rows) columns0 B0)
              (@finite_family_tail (@comm_ring_carrier R) columns0 x0))))
        (@comm_ring_vector_add R rows
          (@comm_ring_matrix_apply R rows (succ columns0) A0 x0)
          (@comm_ring_matrix_apply R rows (succ columns0) B0 x0))
        (@comm_ring_vector_add_congr_path R rows
          _ _ _ _
          (@comm_ring_vector_scale_add_vector_path R rows
            (@finite_family_head (@comm_ring_carrier R) columns0 x0)
            (@finite_family_head (@CommRingVector R rows) columns0 A0)
            (@finite_family_head (@CommRingVector R rows) columns0 B0))
          (ih
            (@finite_family_tail (@CommRingVector R rows) columns0 A0)
            (@finite_family_tail (@CommRingVector R rows) columns0 B0)
            (@finite_family_tail (@comm_ring_carrier R) columns0 x0)))
        (@comm_ring_vector_add_interchange_path R rows
          (@comm_ring_vector_scale R rows
            (@finite_family_head (@comm_ring_carrier R) columns0 x0)
            (@finite_family_head (@CommRingVector R rows) columns0 A0))
          (@comm_ring_vector_scale R rows
            (@finite_family_head (@comm_ring_carrier R) columns0 x0)
            (@finite_family_head (@CommRingVector R rows) columns0 B0))
          (@comm_ring_matrix_apply R rows columns0
            (@finite_family_tail (@CommRingVector R rows) columns0 A0)
            (@finite_family_tail (@comm_ring_carrier R) columns0 x0))
          (@comm_ring_matrix_apply R rows columns0
            (@finite_family_tail (@CommRingVector R rows) columns0 B0)
            (@finite_family_tail (@comm_ring_carrier R) columns0 x0))))
    columns) A B x;

symbol comm_ring_matrix_add_congr_path
  (R : τ CommRing)
  (rows columns : τ Nat_grpd)
  (A A' B B' : τ (@CommRingMatrix R rows columns))
  (p : τ (@= (@CommRingMatrix R rows columns) A A'))
  (q : τ (@= (@CommRingMatrix R rows columns) B B'))
  : τ (@= (@CommRingMatrix R rows columns)
      (@comm_ring_matrix_add R rows columns A B)
      (@comm_ring_matrix_add R rows columns A' B'))
≔ @eq_trans
    (@CommRingMatrix R rows columns)
    (@comm_ring_matrix_add R rows columns A B)
    (@comm_ring_matrix_add R rows columns A' B)
    (@comm_ring_matrix_add R rows columns A' B')
    (@eq_ap
      (@CommRingMatrix R rows columns)
      (@CommRingMatrix R rows columns)
      (λ X : τ (@CommRingMatrix R rows columns),
        @comm_ring_matrix_add R rows columns X B)
      A A' p)
    (@eq_ap
      (@CommRingMatrix R rows columns)
      (@CommRingMatrix R rows columns)
      (λ X : τ (@CommRingMatrix R rows columns),
        @comm_ring_matrix_add R rows columns A' X)
      B B' q);

symbol comm_ring_matrix_add_zero_right_path
  (R : τ CommRing)
  (rows columns : τ Nat_grpd)
  (A : τ (@CommRingMatrix R rows columns))
  : τ (@= (@CommRingMatrix R rows columns)
      (@comm_ring_matrix_add R rows columns A
        (@comm_ring_matrix_zero R rows columns))
      A)
≔ (@nat_elim
    (λ columns0 : τ Nat_grpd,
      @Pi_grpd (@CommRingMatrix R rows columns0) (λ A0 : τ _,
        @= (@CommRingMatrix R rows columns0)
          (@comm_ring_matrix_add R rows columns0 A0
            (@comm_ring_matrix_zero R rows columns0))
          A0))
    (λ A0 : τ _, (sigma_Snd unit_is_contr) A0)
    (λ columns0 : τ Nat_grpd, λ ih : τ _, λ A0 : τ _,
      @finite_family_succ_path
        (@CommRingVector R rows) columns0
        (@comm_ring_matrix_add R rows (succ columns0) A0
          (@comm_ring_matrix_zero R rows (succ columns0)))
        A0
        (@comm_ring_vector_add_zero_right_path R rows
          (@finite_family_head (@CommRingVector R rows) columns0 A0))
        (ih (@finite_family_tail (@CommRingVector R rows) columns0 A0)))
    columns) A;

symbol comm_ring_matrix_add_zero_left_path
  (R : τ CommRing)
  (rows columns : τ Nat_grpd)
  (A : τ (@CommRingMatrix R rows columns))
  : τ (@= (@CommRingMatrix R rows columns)
      (@comm_ring_matrix_add R rows columns
        (@comm_ring_matrix_zero R rows columns) A)
      A)
≔ (@nat_elim
    (λ columns0 : τ Nat_grpd,
      @Pi_grpd (@CommRingMatrix R rows columns0) (λ A0 : τ _,
        @= (@CommRingMatrix R rows columns0)
          (@comm_ring_matrix_add R rows columns0
            (@comm_ring_matrix_zero R rows columns0) A0)
          A0))
    (λ A0 : τ _, (sigma_Snd unit_is_contr) A0)
    (λ columns0 : τ Nat_grpd, λ ih : τ _, λ A0 : τ _,
      @finite_family_succ_path
        (@CommRingVector R rows) columns0
        (@comm_ring_matrix_add R rows (succ columns0)
          (@comm_ring_matrix_zero R rows (succ columns0)) A0)
        A0
        (@comm_ring_vector_add_zero_left_path R rows
          (@finite_family_head (@CommRingVector R rows) columns0 A0))
        (ih (@finite_family_tail (@CommRingVector R rows) columns0 A0)))
    columns) A;

symbol comm_ring_matrix_add_assoc_path
  (R : τ CommRing)
  (rows columns : τ Nat_grpd)
  (A B C : τ (@CommRingMatrix R rows columns))
  : τ (@= (@CommRingMatrix R rows columns)
      (@comm_ring_matrix_add R rows columns
        (@comm_ring_matrix_add R rows columns A B) C)
      (@comm_ring_matrix_add R rows columns A
        (@comm_ring_matrix_add R rows columns B C)))
≔ (@nat_elim
    (λ columns0 : τ Nat_grpd,
      @Pi_grpd (@CommRingMatrix R rows columns0) (λ A0 : τ _,
        @Pi_grpd (@CommRingMatrix R rows columns0) (λ B0 : τ _,
          @Pi_grpd (@CommRingMatrix R rows columns0) (λ C0 : τ _,
            @= (@CommRingMatrix R rows columns0)
              (@comm_ring_matrix_add R rows columns0
                (@comm_ring_matrix_add R rows columns0 A0 B0) C0)
              (@comm_ring_matrix_add R rows columns0 A0
                (@comm_ring_matrix_add R rows columns0 B0 C0))))))
    (λ _ : τ _, λ _ : τ _, λ _ : τ _, @eq_refl Unit_grpd tt)
    (λ columns0 : τ Nat_grpd, λ ih : τ _,
      λ A0 : τ _, λ B0 : τ _, λ C0 : τ _,
      @finite_family_succ_path
        (@CommRingVector R rows) columns0
        (@comm_ring_matrix_add R rows (succ columns0)
          (@comm_ring_matrix_add R rows (succ columns0) A0 B0) C0)
        (@comm_ring_matrix_add R rows (succ columns0) A0
          (@comm_ring_matrix_add R rows (succ columns0) B0 C0))
        (@comm_ring_vector_add_assoc_path R rows
          (@finite_family_head (@CommRingVector R rows) columns0 A0)
          (@finite_family_head (@CommRingVector R rows) columns0 B0)
          (@finite_family_head (@CommRingVector R rows) columns0 C0))
        (ih
          (@finite_family_tail (@CommRingVector R rows) columns0 A0)
          (@finite_family_tail (@CommRingVector R rows) columns0 B0)
          (@finite_family_tail (@CommRingVector R rows) columns0 C0)))
    columns) A B C;

symbol comm_ring_matrix_add_comm_path
  (R : τ CommRing)
  (rows columns : τ Nat_grpd)
  (A B : τ (@CommRingMatrix R rows columns))
  : τ (@= (@CommRingMatrix R rows columns)
      (@comm_ring_matrix_add R rows columns A B)
      (@comm_ring_matrix_add R rows columns B A))
≔ (@nat_elim
    (λ columns0 : τ Nat_grpd,
      @Pi_grpd (@CommRingMatrix R rows columns0) (λ A0 : τ _,
        @Pi_grpd (@CommRingMatrix R rows columns0) (λ B0 : τ _,
          @= (@CommRingMatrix R rows columns0)
            (@comm_ring_matrix_add R rows columns0 A0 B0)
            (@comm_ring_matrix_add R rows columns0 B0 A0))))
    (λ _ : τ _, λ _ : τ _, @eq_refl Unit_grpd tt)
    (λ columns0 : τ Nat_grpd, λ ih : τ _, λ A0 : τ _, λ B0 : τ _,
      @finite_family_succ_path
        (@CommRingVector R rows) columns0
        (@comm_ring_matrix_add R rows (succ columns0) A0 B0)
        (@comm_ring_matrix_add R rows (succ columns0) B0 A0)
        (@comm_ring_vector_add_comm_path R rows
          (@finite_family_head (@CommRingVector R rows) columns0 A0)
          (@finite_family_head (@CommRingVector R rows) columns0 B0))
        (ih
          (@finite_family_tail (@CommRingVector R rows) columns0 A0)
          (@finite_family_tail (@CommRingVector R rows) columns0 B0)))
    columns) A B;

symbol comm_ring_matrix_add_inv_path
  (R : τ CommRing)
  (rows columns : τ Nat_grpd)
  (A : τ (@CommRingMatrix R rows columns))
  : τ (@= (@CommRingMatrix R rows columns)
      (@comm_ring_matrix_add R rows columns A
        (@comm_ring_matrix_neg R rows columns A))
      (@comm_ring_matrix_zero R rows columns))
≔ (@nat_elim
    (λ columns0 : τ Nat_grpd,
      @Pi_grpd (@CommRingMatrix R rows columns0) (λ A0 : τ _,
        @= (@CommRingMatrix R rows columns0)
          (@comm_ring_matrix_add R rows columns0 A0
            (@comm_ring_matrix_neg R rows columns0 A0))
          (@comm_ring_matrix_zero R rows columns0)))
    (λ _ : τ _, @eq_refl Unit_grpd tt)
    (λ columns0 : τ Nat_grpd, λ ih : τ _, λ A0 : τ _,
      @finite_family_succ_path
        (@CommRingVector R rows) columns0
        (@comm_ring_matrix_add R rows (succ columns0) A0
          (@comm_ring_matrix_neg R rows (succ columns0) A0))
        (@comm_ring_matrix_zero R rows (succ columns0))
        (@comm_ring_vector_add_inv_path R rows
          (@finite_family_head (@CommRingVector R rows) columns0 A0))
        (ih (@finite_family_tail (@CommRingVector R rows) columns0 A0)))
    columns) A;

symbol comm_ring_matrix_comp_zero_right_path
  (R : τ CommRing)
  (rows middle columns : τ Nat_grpd)
  (A : τ (@CommRingMatrix R rows middle))
  : τ (@= (@CommRingMatrix R rows columns)
      (@comm_ring_matrix_comp R rows middle columns A
        (@comm_ring_matrix_zero R middle columns))
      (@comm_ring_matrix_zero R rows columns))
≔ @nat_elim
    (λ columns0 : τ Nat_grpd,
      @= (@CommRingMatrix R rows columns0)
        (@comm_ring_matrix_comp R rows middle columns0 A
          (@comm_ring_matrix_zero R middle columns0))
        (@comm_ring_matrix_zero R rows columns0))
    (@eq_refl (@CommRingMatrix R rows zero)
      (@finite_family_nil (@CommRingVector R rows)))
    (λ columns0 : τ Nat_grpd, λ ih : τ _,
      @finite_family_succ_path
        (@CommRingVector R rows) columns0
        (@comm_ring_matrix_comp R rows middle (succ columns0) A
          (@comm_ring_matrix_zero R middle (succ columns0)))
        (@comm_ring_matrix_zero R rows (succ columns0))
        (@comm_ring_matrix_apply_zero_vector_path R rows middle A)
        ih)
    columns;

symbol comm_ring_matrix_comp_zero_left_path
  (R : τ CommRing)
  (rows middle columns : τ Nat_grpd)
  (B : τ (@CommRingMatrix R middle columns))
  : τ (@= (@CommRingMatrix R rows columns)
      (@comm_ring_matrix_comp R rows middle columns
        (@comm_ring_matrix_zero R rows middle) B)
      (@comm_ring_matrix_zero R rows columns))
≔ (@nat_elim
    (λ columns0 : τ Nat_grpd,
      @Pi_grpd (@CommRingMatrix R middle columns0) (λ B0 : τ _,
        @= (@CommRingMatrix R rows columns0)
          (@comm_ring_matrix_comp R rows middle columns0
            (@comm_ring_matrix_zero R rows middle) B0)
          (@comm_ring_matrix_zero R rows columns0)))
    (λ _ : τ _, @eq_refl (@CommRingMatrix R rows zero)
      (@finite_family_nil (@CommRingVector R rows)))
    (λ columns0 : τ Nat_grpd, λ ih : τ _, λ B0 : τ _,
      @finite_family_succ_path
        (@CommRingVector R rows) columns0
        (@comm_ring_matrix_comp R rows middle (succ columns0)
          (@comm_ring_matrix_zero R rows middle) B0)
        (@comm_ring_matrix_zero R rows (succ columns0))
        (@comm_ring_matrix_apply_zero_matrix_path R rows middle
          (@finite_family_head (@CommRingVector R middle) columns0 B0))
        (ih (@finite_family_tail (@CommRingVector R middle) columns0 B0)))
    columns) B;

symbol comm_ring_matrix_comp_add_right_path
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
≔ (@nat_elim
    (λ columns0 : τ Nat_grpd,
      @Pi_grpd (@CommRingMatrix R middle columns0) (λ B0 : τ _,
        @Pi_grpd (@CommRingMatrix R middle columns0) (λ C0 : τ _,
          @= (@CommRingMatrix R rows columns0)
            (@comm_ring_matrix_comp R rows middle columns0 A
              (@comm_ring_matrix_add R middle columns0 B0 C0))
            (@comm_ring_matrix_add R rows columns0
              (@comm_ring_matrix_comp R rows middle columns0 A B0)
              (@comm_ring_matrix_comp R rows middle columns0 A C0)))))
    (λ _ : τ _, λ _ : τ _, @eq_refl Unit_grpd tt)
    (λ columns0 : τ Nat_grpd, λ ih : τ _, λ B0 : τ _, λ C0 : τ _,
      @finite_family_succ_path
        (@CommRingVector R rows) columns0
        (@comm_ring_matrix_comp R rows middle (succ columns0) A
          (@comm_ring_matrix_add R middle (succ columns0) B0 C0))
        (@comm_ring_matrix_add R rows (succ columns0)
          (@comm_ring_matrix_comp R rows middle (succ columns0) A B0)
          (@comm_ring_matrix_comp R rows middle (succ columns0) A C0))
        (@comm_ring_matrix_apply_add_vector_path R rows middle A
          (@finite_family_head (@CommRingVector R middle) columns0 B0)
          (@finite_family_head (@CommRingVector R middle) columns0 C0))
        (ih
          (@finite_family_tail (@CommRingVector R middle) columns0 B0)
          (@finite_family_tail (@CommRingVector R middle) columns0 C0)))
    columns) B C;

symbol comm_ring_matrix_comp_add_left_path
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
≔ (@nat_elim
    (λ columns0 : τ Nat_grpd,
      @Pi_grpd (@CommRingMatrix R middle columns0) (λ C0 : τ _,
        @= (@CommRingMatrix R rows columns0)
          (@comm_ring_matrix_comp R rows middle columns0
            (@comm_ring_matrix_add R rows middle A B) C0)
          (@comm_ring_matrix_add R rows columns0
            (@comm_ring_matrix_comp R rows middle columns0 A C0)
            (@comm_ring_matrix_comp R rows middle columns0 B C0))))
    (λ _ : τ _, @eq_refl Unit_grpd tt)
    (λ columns0 : τ Nat_grpd, λ ih : τ _, λ C0 : τ _,
      @finite_family_succ_path
        (@CommRingVector R rows) columns0
        (@comm_ring_matrix_comp R rows middle (succ columns0)
          (@comm_ring_matrix_add R rows middle A B) C0)
        (@comm_ring_matrix_add R rows (succ columns0)
          (@comm_ring_matrix_comp R rows middle (succ columns0) A C0)
          (@comm_ring_matrix_comp R rows middle (succ columns0) B C0))
        (@comm_ring_matrix_apply_add_matrix_path R rows middle A B
          (@finite_family_head (@CommRingVector R middle) columns0 C0))
        (ih (@finite_family_tail (@CommRingVector R middle) columns0 C0)))
    columns) C;
