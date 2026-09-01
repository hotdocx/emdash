/*
  Selected triangular binary products in the finite-free matrix category.

  The product functor is the existing whole direct-sum functor. Narrow stable
  point observations expose the canonical matrix projections and vertical
  pairing, while generic triangular transfors retain higher action and own
  Došen beta/eta computation.
*/

require open emdash.emdash3_2_commutative_algebra_finite_free_direct_sums;
require open emdash.emdash3_2_triangular_binary_products;

injective symbol comm_ring_finite_free_binary_products
  (R : τ CommRing)
  : τ (@BinaryProducts
      (@CommRingFiniteFree_cat R)
      (@comm_ring_finite_free_direct_sum_func R));

injective symbol comm_ring_finite_free_binary_proj1
  [R : τ CommRing]
  (m n : τ Nat_grpd)
  : τ (@CommRingMatrix R m (@nat_add m n));

injective symbol comm_ring_finite_free_binary_proj2
  [R : τ CommRing]
  (m n : τ Nat_grpd)
  : τ (@CommRingMatrix R n (@nat_add m n));

injective symbol comm_ring_finite_free_binary_pair
  [R : τ CommRing]
  [x m n : τ Nat_grpd]
  (f : τ (@CommRingMatrix R m x))
  (g : τ (@CommRingMatrix R n x))
  : τ (@CommRingMatrix R (@nat_add m n) x);

unif_rule
  @binary_products_proj1_fapp0
      _ _ (@comm_ring_finite_free_binary_products $R) $m $n
  ≡ @comm_ring_finite_free_binary_proj1 $R $m $n
  ↪ [ tt ≡ tt ];

unif_rule
  @binary_products_proj2_fapp0
      _ _ (@comm_ring_finite_free_binary_products $R) $m $n
  ≡ @comm_ring_finite_free_binary_proj2 $R $m $n
  ↪ [ tt ≡ tt ];

unif_rule
  @binary_products_pair_fapp0
      _ _ (@comm_ring_finite_free_binary_products $R)
      $x $m $n $f $g
  ≡ @comm_ring_finite_free_binary_pair $R $x $m $n $f $g
  ↪ [ tt ≡ tt ];

symbol comm_ring_finite_free_binary_proj1_path
  [R : τ CommRing]
  (m n : τ Nat_grpd)
  : τ (@= (@CommRingMatrix R m (@nat_add m n))
      (@binary_products_proj1_fapp0
        (@CommRingFiniteFree_cat R)
        (@comm_ring_finite_free_direct_sum_func R)
        (@comm_ring_finite_free_binary_products R) m n)
      (@comm_ring_finite_free_binary_proj1 R m n))
≔ @eq_refl _
    (@binary_products_proj1_fapp0
      (@CommRingFiniteFree_cat R)
      (@comm_ring_finite_free_direct_sum_func R)
      (@comm_ring_finite_free_binary_products R) m n);

symbol comm_ring_finite_free_binary_proj2_path
  [R : τ CommRing]
  (m n : τ Nat_grpd)
  : τ (@= (@CommRingMatrix R n (@nat_add m n))
      (@binary_products_proj2_fapp0
        (@CommRingFiniteFree_cat R)
        (@comm_ring_finite_free_direct_sum_func R)
        (@comm_ring_finite_free_binary_products R) m n)
      (@comm_ring_finite_free_binary_proj2 R m n))
≔ @eq_refl _
    (@binary_products_proj2_fapp0
      (@CommRingFiniteFree_cat R)
      (@comm_ring_finite_free_direct_sum_func R)
      (@comm_ring_finite_free_binary_products R) m n);

symbol comm_ring_finite_free_binary_pair_path
  [R : τ CommRing]
  [x m n : τ Nat_grpd]
  (f : τ (@CommRingMatrix R m x))
  (g : τ (@CommRingMatrix R n x))
  : τ (@= (@CommRingMatrix R (@nat_add m n) x)
      (@binary_products_pair_fapp0
        (@CommRingFiniteFree_cat R)
        (@comm_ring_finite_free_direct_sum_func R)
        (@comm_ring_finite_free_binary_products R) x m n f g)
      (@comm_ring_finite_free_binary_pair R x m n f g))
≔ @eq_refl _
    (@binary_products_pair_fapp0
      (@CommRingFiniteFree_cat R)
      (@comm_ring_finite_free_direct_sum_func R)
      (@comm_ring_finite_free_binary_products R) x m n f g);

rule @comm_ring_finite_free_binary_proj1 $R $m $n
  ↪ @comm_ring_matrix_proj1 $R $m $n;

rule @comm_ring_finite_free_binary_proj2 $R $m $n
  ↪ @comm_ring_matrix_proj2 $R $m $n;

rule @comm_ring_finite_free_binary_pair $R $x $m $n $f $g
  ↪ @comm_ring_matrix_vertical $R $m $n $x $f $g;
