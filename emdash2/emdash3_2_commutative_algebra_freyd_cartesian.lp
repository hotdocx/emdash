/*
  Selected Cartesian structure on the formal Freyd category.

  This is the transparent pairing of the already-computational binary-product
  and terminal-zero capabilities. It adds no rule or duplicate operation.
*/

require open emdash.emdash3_2_commutative_algebra_freyd_terminal_zero;
require open emdash.emdash3_2_cartesian_categories;

symbol comm_ring_freyd_cartesian
  (R : τ CommRing)
  : τ (@CartesianCategory
      (@CommRingFreydPresentation_cat R)
      (@comm_ring_freyd_direct_sum_func R)
      (@comm_ring_zero_presentation R))
≔ @cartesian_category_intro
    (@CommRingFreydPresentation_cat R)
    (@comm_ring_freyd_direct_sum_func R)
    (@comm_ring_zero_presentation R)
    (@comm_ring_freyd_binary_products R)
    (@comm_ring_freyd_terminal_zero R);
