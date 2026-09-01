/* Selected Cartesian structure on the finite-free matrix category. */

require open emdash.emdash3_2_commutative_algebra_finite_free_terminal_zero;
require open emdash.emdash3_2_cartesian_categories;

symbol comm_ring_finite_free_cartesian
  (R : τ CommRing)
  : τ (@CartesianCategory
      (@CommRingFiniteFree_cat R)
      (@comm_ring_finite_free_direct_sum_func R)
      zero)
≔ @cartesian_category_intro
    (@CommRingFiniteFree_cat R)
    (@comm_ring_finite_free_direct_sum_func R)
    zero
    (@comm_ring_finite_free_binary_products R)
    (@comm_ring_finite_free_terminal_zero R);
