/* Reviewer-facing whole finite-free direct sums. */

require open emdash.emdash3_2_commutative_algebra_finite_free_direct_sums;

assert (R : τ CommRing) ⊢
  @comm_ring_finite_free_direct_sum_func R
  : τ (@Functor
      (Product_cat
        (@CommRingFiniteFree_cat R)
        (@CommRingFiniteFree_cat R))
      (@CommRingFiniteFree_cat R));

assert (R : τ CommRing)
  (m n : τ Nat_grpd) ⊢
  @fapp0
    (Product_cat (@CommRingFiniteFree_cat R) (@CommRingFiniteFree_cat R))
    (@CommRingFiniteFree_cat R)
    (@comm_ring_finite_free_direct_sum_func R)
    (Struct_sigma m n)
  ≡ @nat_add m n;

assert (R : τ CommRing)
  (m0 n0 m1 n1 : τ Nat_grpd)
  (f : τ (@CommRingMatrix R m1 m0))
  (g : τ (@CommRingMatrix R n1 n0)) ⊢
  @fapp1_fapp0
    (Product_cat (@CommRingFiniteFree_cat R) (@CommRingFiniteFree_cat R))
    (@CommRingFiniteFree_cat R)
    (@comm_ring_finite_free_direct_sum_func R)
    (Struct_sigma m0 n0)
    (Struct_sigma m1 n1)
    (Struct_sigma f g)
  ≡ @comm_ring_matrix_block_diag R m1 n1 m0 n0 f g;

assert (R : τ CommRing)
  (m0 n0 m1 n1 : τ Nat_grpd) ⊢
  @comm_ring_finite_free_direct_sum_hom_func R m0 n0 m1 n1
  : τ (@Functor
      (Hom_cat
        (Product_cat
          (@CommRingFiniteFree_cat R)
          (@CommRingFiniteFree_cat R))
        (Struct_sigma m0 n0)
        (Struct_sigma m1 n1))
      (Hom_cat (@CommRingFiniteFree_cat R)
        (@nat_add m0 n0) (@nat_add m1 n1)));

assertnot (R : τ CommRing)
  (m0 n0 m1 n1 : τ Nat_grpd)
  (f f' : τ (@CommRingMatrix R m1 m0))
  (g : τ (@CommRingMatrix R n1 n0)) ⊢
  @comm_ring_matrix_block_diag R m1 n1 m0 n0 f g
  ≡ @comm_ring_matrix_block_diag R m1 n1 m0 n0 f' g;
