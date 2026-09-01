/*
  Reusable element-level consequences of the commutative-ring law basis.

  The base structure retains right additive unit/inverse, commutative
  multiplication, and left distributivity. This rule-free module derives the
  opposite additive orientations, right distributivity, multiplication by
  zero, and negation of zero. Matrix algebra and localization reuse these
  theorem paths; no new runtime normalization is installed.
*/

require open emdash.emdash3_2_commutative_algebra;

symbol comm_ring_add_zero_left_path
  (R : τ CommRing)
  (x : τ (@comm_ring_carrier R))
  : τ (@= (@comm_ring_carrier R)
      (@comm_ring_add R (@comm_ring_zero R) x)
      x)
≔ @eq_trans
    (@comm_ring_carrier R)
    (@comm_ring_add R (@comm_ring_zero R) x)
    (@comm_ring_add R x (@comm_ring_zero R))
    x
    ((@comm_ring_add_comm_law R) (@comm_ring_zero R) x)
    ((@comm_ring_add_zero_law R) x);

symbol comm_ring_add_inv_left_path
  (R : τ CommRing)
  (x : τ (@comm_ring_carrier R))
  : τ (@= (@comm_ring_carrier R)
      (@comm_ring_add R (@comm_ring_neg R x) x)
      (@comm_ring_zero R))
≔ @eq_trans
    (@comm_ring_carrier R)
    (@comm_ring_add R (@comm_ring_neg R x) x)
    (@comm_ring_add R x (@comm_ring_neg R x))
    (@comm_ring_zero R)
    ((@comm_ring_add_comm_law R) (@comm_ring_neg R x) x)
    ((@comm_ring_add_inv_law R) x);

// Right distributivity follows from multiplicative commutativity.
symbol comm_ring_right_distrib_path
  (R : τ CommRing)
  (x y z : τ (@comm_ring_carrier R))
  : τ (@= (@comm_ring_carrier R)
      (@comm_ring_mul R (@comm_ring_add R x y) z)
      (@comm_ring_add R
        (@comm_ring_mul R x z)
        (@comm_ring_mul R y z)))
≔ @eq_trans
    (@comm_ring_carrier R)
    (@comm_ring_mul R (@comm_ring_add R x y) z)
    (@comm_ring_mul R z (@comm_ring_add R x y))
    (@comm_ring_add R
      (@comm_ring_mul R x z)
      (@comm_ring_mul R y z))
    ((@comm_ring_mul_comm_law R) (@comm_ring_add R x y) z)
    (@eq_trans
      (@comm_ring_carrier R)
      (@comm_ring_mul R z (@comm_ring_add R x y))
      (@comm_ring_add R
        (@comm_ring_mul R z x)
        (@comm_ring_mul R z y))
      (@comm_ring_add R
        (@comm_ring_mul R x z)
        (@comm_ring_mul R y z))
      ((@comm_ring_left_distrib_law R) z x y)
      (@eq_trans
        (@comm_ring_carrier R)
        (@comm_ring_add R
          (@comm_ring_mul R z x)
          (@comm_ring_mul R z y))
        (@comm_ring_add R
          (@comm_ring_mul R x z)
          (@comm_ring_mul R z y))
        (@comm_ring_add R
          (@comm_ring_mul R x z)
          (@comm_ring_mul R y z))
        (@eq_ap
          (@comm_ring_carrier R)
          (@comm_ring_carrier R)
          (λ u : τ (@comm_ring_carrier R),
            @comm_ring_add R u (@comm_ring_mul R z y))
          (@comm_ring_mul R z x)
          (@comm_ring_mul R x z)
          ((@comm_ring_mul_comm_law R) z x))
        (@eq_ap
          (@comm_ring_carrier R)
          (@comm_ring_carrier R)
          (λ v : τ (@comm_ring_carrier R),
            @comm_ring_add R (@comm_ring_mul R x z) v)
          (@comm_ring_mul R z y)
          (@comm_ring_mul R y z)
          ((@comm_ring_mul_comm_law R) z y))));

// If a+a=a in the additive group, then a=0.
protected symbol comm_ring_add_idempotent_reduction_path
  (R : τ CommRing)
  (a : τ (@comm_ring_carrier R))
  : τ (@=
      (@comm_ring_carrier R)
      (@comm_ring_add R
        (@comm_ring_add R a a)
        (@comm_ring_neg R a))
      a)
≔ @eq_trans
    (@comm_ring_carrier R)
    (@comm_ring_add R
      (@comm_ring_add R a a)
      (@comm_ring_neg R a))
    (@comm_ring_add R
      a
      (@comm_ring_add R a (@comm_ring_neg R a)))
    a
    ((@comm_ring_add_assoc_law R) a a (@comm_ring_neg R a))
    (@eq_trans
      (@comm_ring_carrier R)
      (@comm_ring_add R
        a
        (@comm_ring_add R a (@comm_ring_neg R a)))
      (@comm_ring_add R a (@comm_ring_zero R))
      a
      (@eq_ap
        (@comm_ring_carrier R)
        (@comm_ring_carrier R)
        (λ z : τ (@comm_ring_carrier R), @comm_ring_add R a z)
        (@comm_ring_add R a (@comm_ring_neg R a))
        (@comm_ring_zero R)
        ((@comm_ring_add_inv_law R) a))
      ((@comm_ring_add_zero_law R) a));

symbol comm_ring_add_idempotent_is_zero_path
  (R : τ CommRing)
  (a : τ (@comm_ring_carrier R))
  (idempotent : τ (@=
      (@comm_ring_carrier R)
      (@comm_ring_add R a a)
      a))
  : τ (@= (@comm_ring_carrier R) a (@comm_ring_zero R))
≔ @eq_trans
    (@comm_ring_carrier R)
    a
    (@comm_ring_add R
      (@comm_ring_add R a a)
      (@comm_ring_neg R a))
    (@comm_ring_zero R)
    (@eq_sym
      (@comm_ring_carrier R)
      (@comm_ring_add R
        (@comm_ring_add R a a)
        (@comm_ring_neg R a))
      a
      (@comm_ring_add_idempotent_reduction_path R a))
    (@eq_trans
      (@comm_ring_carrier R)
      (@comm_ring_add R
        (@comm_ring_add R a a)
        (@comm_ring_neg R a))
      (@comm_ring_add R a (@comm_ring_neg R a))
      (@comm_ring_zero R)
      (@eq_ap
        (@comm_ring_carrier R)
        (@comm_ring_carrier R)
        (λ z : τ (@comm_ring_carrier R),
          @comm_ring_add R z (@comm_ring_neg R a))
        (@comm_ring_add R a a)
        a
        idempotent)
      ((@comm_ring_add_inv_law R) a));

symbol comm_ring_mul_zero_right_path
  (R : τ CommRing)
  (x : τ (@comm_ring_carrier R))
  : τ (@= (@comm_ring_carrier R)
      (@comm_ring_mul R x (@comm_ring_zero R))
      (@comm_ring_zero R))
≔ @comm_ring_add_idempotent_is_zero_path
    R
    (@comm_ring_mul R x (@comm_ring_zero R))
    (@eq_trans
      (@comm_ring_carrier R)
      (@comm_ring_add R
        (@comm_ring_mul R x (@comm_ring_zero R))
        (@comm_ring_mul R x (@comm_ring_zero R)))
      (@comm_ring_mul R x
        (@comm_ring_add R (@comm_ring_zero R) (@comm_ring_zero R)))
      (@comm_ring_mul R x (@comm_ring_zero R))
      (@eq_sym
        (@comm_ring_carrier R)
        (@comm_ring_mul R x
          (@comm_ring_add R (@comm_ring_zero R) (@comm_ring_zero R)))
        (@comm_ring_add R
          (@comm_ring_mul R x (@comm_ring_zero R))
          (@comm_ring_mul R x (@comm_ring_zero R)))
        ((@comm_ring_left_distrib_law R)
          x (@comm_ring_zero R) (@comm_ring_zero R)))
      (@eq_ap
        (@comm_ring_carrier R)
        (@comm_ring_carrier R)
        (λ z : τ (@comm_ring_carrier R), @comm_ring_mul R x z)
        (@comm_ring_add R (@comm_ring_zero R) (@comm_ring_zero R))
        (@comm_ring_zero R)
        ((@comm_ring_add_zero_law R) (@comm_ring_zero R))));

symbol comm_ring_mul_zero_left_path
  (R : τ CommRing)
  (x : τ (@comm_ring_carrier R))
  : τ (@= (@comm_ring_carrier R)
      (@comm_ring_mul R (@comm_ring_zero R) x)
      (@comm_ring_zero R))
≔ @eq_trans
    (@comm_ring_carrier R)
    (@comm_ring_mul R (@comm_ring_zero R) x)
    (@comm_ring_mul R x (@comm_ring_zero R))
    (@comm_ring_zero R)
    ((@comm_ring_mul_comm_law R) (@comm_ring_zero R) x)
    (@comm_ring_mul_zero_right_path R x);

symbol comm_ring_neg_zero_path
  (R : τ CommRing)
  : τ (@= (@comm_ring_carrier R)
      (@comm_ring_zero R)
      (@comm_ring_neg R (@comm_ring_zero R)))
≔ @eq_trans
    (@comm_ring_carrier R)
    (@comm_ring_zero R)
    (@comm_ring_add R
      (@comm_ring_zero R)
      (@comm_ring_neg R (@comm_ring_zero R)))
    (@comm_ring_neg R (@comm_ring_zero R))
    (@eq_sym
      (@comm_ring_carrier R)
      (@comm_ring_add R
        (@comm_ring_zero R)
        (@comm_ring_neg R (@comm_ring_zero R)))
      (@comm_ring_zero R)
      ((@comm_ring_add_inv_law R) (@comm_ring_zero R)))
    (@eq_trans
      (@comm_ring_carrier R)
      (@comm_ring_add R
        (@comm_ring_zero R)
        (@comm_ring_neg R (@comm_ring_zero R)))
      (@comm_ring_add R
        (@comm_ring_neg R (@comm_ring_zero R))
        (@comm_ring_zero R))
      (@comm_ring_neg R (@comm_ring_zero R))
      ((@comm_ring_add_comm_law R)
        (@comm_ring_zero R)
        (@comm_ring_neg R (@comm_ring_zero R)))
      ((@comm_ring_add_zero_law R)
        (@comm_ring_neg R (@comm_ring_zero R))));
