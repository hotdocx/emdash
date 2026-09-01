/* Reviewer-facing Cartesian structure on the formal Freyd category. */

require open emdash.emdash3_2_commutative_algebra_freyd_cartesian;

assert (R : τ CommRing) ⊢
  @comm_ring_freyd_cartesian R
  : τ (@CartesianCategory
      (@CommRingFreydPresentation_cat R)
      (@comm_ring_freyd_direct_sum_func R)
      (@comm_ring_zero_presentation R));

assert (R : τ CommRing) ⊢
  @cartesian_binary_products
    (@CommRingFreydPresentation_cat R)
    (@comm_ring_freyd_direct_sum_func R)
    (@comm_ring_zero_presentation R)
    (@comm_ring_freyd_cartesian R)
  ≡ @comm_ring_freyd_binary_products R;

assert (R : τ CommRing) ⊢
  @cartesian_terminal_object
    (@CommRingFreydPresentation_cat R)
    (@comm_ring_freyd_direct_sum_func R)
    (@comm_ring_zero_presentation R)
    (@comm_ring_freyd_cartesian R)
  ≡ @comm_ring_freyd_terminal_zero R;
