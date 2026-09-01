/* Additive structure on the finite-free matrix category. */

require open emdash.emdash3_2_additive_categories;
require open emdash.emdash3_2_commutative_algebra_finite_free_preadditive;
require open emdash.emdash3_2_commutative_algebra_finite_free_cartesian;

symbol comm_ring_finite_free_additive
  (R : τ CommRing)
  : τ (@AdditiveCategory
      (@CommRingFiniteFree_cat R)
      (@comm_ring_finite_free_direct_sum_func R)
      zero)
≔ @additive_category_intro
    (@CommRingFiniteFree_cat R)
    (@comm_ring_finite_free_direct_sum_func R)
    zero
    (@comm_ring_finite_free_preadditive R)
    (@comm_ring_finite_free_cartesian R);
