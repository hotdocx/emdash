/*
  Whole direct sums in the finite-free matrix category.

  Rank addition is the object action and flattened block diagonal is the
  arrow action. The whole functor remains available at every Hom level. Its
  object and first-arrow computations are narrow constructor observations;
  generic functorial identity/composition remain globally owned. Constructed
  matrix paths record the corresponding semantic joins.
*/

require open emdash.emdash3_2_commutative_algebra_matrix_block_laws;

injective symbol comm_ring_finite_free_direct_sum_func
  (R : τ CommRing)
  : τ (@Functor
      (Product_cat
        (@CommRingFiniteFree_cat R)
        (@CommRingFiniteFree_cat R))
      (@CommRingFiniteFree_cat R));

// Object action `(m,n) |-> m+n`; the ring is reconstructible and unused.
rule @fapp0 _ _
      (@comm_ring_finite_free_direct_sum_func _)
      (Struct_sigma $m $n)
  ↪ @nat_add $m $n;

// First-arrow action is the flattened block diagonal of the two matrices.
rule @fapp1_fapp0 _ _
      (@comm_ring_finite_free_direct_sum_func $R)
      (Struct_sigma $m0 $n0)
      (Struct_sigma $m1 $n1)
      (Struct_sigma $f $g)
  ↪ @comm_ring_matrix_block_diag
      $R $m1 $n1 $m0 $n0 $f $g;

// Readable proof that the selected action exposes block-diagonal computation.
symbol comm_ring_finite_free_direct_sum_action_path
  (R : τ CommRing)
  (m0 n0 m1 n1 : τ Nat_grpd)
  (f : τ (@CommRingMatrix R m1 m0))
  (g : τ (@CommRingMatrix R n1 n0))
  : τ (@= (@CommRingMatrix R
      (@nat_add m1 n1) (@nat_add m0 n0))
      (@fapp1_fapp0
        (Product_cat
          (@CommRingFiniteFree_cat R)
          (@CommRingFiniteFree_cat R))
        (@CommRingFiniteFree_cat R)
        (@comm_ring_finite_free_direct_sum_func R)
        (Struct_sigma m0 n0)
        (Struct_sigma m1 n1)
        (Struct_sigma f g))
      (@comm_ring_matrix_block_diag R m1 n1 m0 n0 f g))
≔ @eq_refl
    (@CommRingMatrix R (@nat_add m1 n1) (@nat_add m0 n0))
    (@fapp1_fapp0
      (Product_cat
        (@CommRingFiniteFree_cat R)
        (@CommRingFiniteFree_cat R))
      (@CommRingFiniteFree_cat R)
      (@comm_ring_finite_free_direct_sum_func R)
      (Struct_sigma m0 n0)
      (Struct_sigma m1 n1)
      (Struct_sigma f g));

// Semantic identity join for the block-diagonal action.
symbol comm_ring_finite_free_direct_sum_id_path
  (R : τ CommRing)
  (m n : τ Nat_grpd)
  : τ (@= (@CommRingMatrix R (@nat_add m n) (@nat_add m n))
      (@comm_ring_matrix_block_diag R m n m n
        (@comm_ring_finite_free_id_matrix R m)
        (@comm_ring_finite_free_id_matrix R n))
      (@comm_ring_finite_free_id_matrix R (@nat_add m n)))
≔ @comm_ring_matrix_block_diag_id_path R m n;

// Semantic composition join for the block-diagonal action.
symbol comm_ring_finite_free_direct_sum_comp_path
  (R : τ CommRing)
  (m0 n0 m1 n1 m2 n2 : τ Nat_grpd)
  (f : τ (@CommRingMatrix R m1 m0))
  (g : τ (@CommRingMatrix R n1 n0))
  (h : τ (@CommRingMatrix R m2 m1))
  (k : τ (@CommRingMatrix R n2 n1))
  : τ (@= (@CommRingMatrix R
      (@nat_add m2 n2) (@nat_add m0 n0))
      (@comm_ring_matrix_comp R
        (@nat_add m2 n2) (@nat_add m1 n1) (@nat_add m0 n0)
        (@comm_ring_matrix_block_diag R m2 n2 m1 n1 h k)
        (@comm_ring_matrix_block_diag R m1 n1 m0 n0 f g))
      (@comm_ring_matrix_block_diag R m2 n2 m0 n0
        (@comm_ring_matrix_comp R m2 m1 m0 h f)
        (@comm_ring_matrix_comp R n2 n1 n0 k g)))
≔ @comm_ring_matrix_block_diag_comp_path
    R m2 n2 m1 n1 m0 n0 h k f g;

// The first Hom action of the whole direct-sum functor remains iterable.
symbol comm_ring_finite_free_direct_sum_hom_func
  [R : τ CommRing]
  [m0 n0 m1 n1 : τ Nat_grpd]
  : τ (@Functor
      (Hom_cat
        (Product_cat
          (@CommRingFiniteFree_cat R)
          (@CommRingFiniteFree_cat R))
        (Struct_sigma m0 n0)
        (Struct_sigma m1 n1))
      (Hom_cat
        (@CommRingFiniteFree_cat R)
        (@nat_add m0 n0)
        (@nat_add m1 n1)))
≔ @fapp1_func
    (Product_cat
      (@CommRingFiniteFree_cat R)
      (@CommRingFiniteFree_cat R))
    (@CommRingFiniteFree_cat R)
    (@comm_ring_finite_free_direct_sum_func R)
    (Struct_sigma m0 n0)
    (Struct_sigma m1 n1);
