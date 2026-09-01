/*
  Additive structure on the formal Freyd presentation category.

  The instance transparently pairs the existing full preadditive evidence with
  the selected computational Cartesian evidence. All zero-object and
  biproduct consequences are inherited from the generic additive theorem
  layer; no concrete duplicate coproduct theory is added.
*/

require open emdash.emdash3_2_additive_categories;
require open emdash.emdash3_2_commutative_algebra_freyd_cartesian;

symbol comm_ring_freyd_additive
  (R : τ CommRing)
  : τ (@AdditiveCategory
      (@CommRingFreydPresentation_cat R)
      (@comm_ring_freyd_direct_sum_func R)
      (@comm_ring_zero_presentation R))
≔ @additive_category_intro
    (@CommRingFreydPresentation_cat R)
    (@comm_ring_freyd_direct_sum_func R)
    (@comm_ring_zero_presentation R)
    (@comm_ring_freyd_preadditive R)
    (@comm_ring_freyd_cartesian R);
