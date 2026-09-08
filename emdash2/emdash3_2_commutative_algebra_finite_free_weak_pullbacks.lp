/*
  Selected finite-free weak pullbacks with explicit constructor data.

  These transparent specializations retain the original difference-cone and
  weak-kernel factor operation/law. Literal ranks and projection matrices
  compute through the existing Sigma and product constructors. Universal
  factor operations are inputs, not inferred from finitely many equations.
*/

require open emdash.emdash3_2_computational_weak_pullback_cones;
require open emdash.emdash3_2_commutative_algebra_finite_free_additive;

// Finite-free specialization of the original whole weak-pullback owner.
symbol CommRingFiniteFreeWeakPullback [R : τ CommRing]
  [x y z : τ Nat_grpd]
  (a : τ (@CommRingMatrix R y x))
  (b : τ (@CommRingMatrix R y z)) : Grpd
≔ @ComputationalWeakPullback
    (@CommRingFiniteFree_cat R)
    (@comm_ring_finite_free_direct_sum_func R) zero
    (@comm_ring_finite_free_additive R) x y z a b;

symbol comm_ring_finite_free_weak_pullback_rank [R : τ CommRing]
  [x y z : τ Nat_grpd]
  [a : τ (@CommRingMatrix R y x)]
  [b : τ (@CommRingMatrix R y z)]
  (U : τ (@CommRingFiniteFreeWeakPullback R x y z a b)) : τ Nat_grpd
≔ @computational_weak_pullback_object
    (@CommRingFiniteFree_cat R)
    (@comm_ring_finite_free_direct_sum_func R) zero
    (@comm_ring_finite_free_additive R) x y z a b U;

symbol comm_ring_finite_free_weak_pullback_proj1 [R : τ CommRing]
  [x y z : τ Nat_grpd]
  [a : τ (@CommRingMatrix R y x)]
  [b : τ (@CommRingMatrix R y z)]
  (U : τ (@CommRingFiniteFreeWeakPullback R x y z a b))
  : τ (@CommRingMatrix R x (@comm_ring_finite_free_weak_pullback_rank R x y z a b U))
≔ @computational_weak_pullback_proj1
    (@CommRingFiniteFree_cat R)
    (@comm_ring_finite_free_direct_sum_func R) zero
    (@comm_ring_finite_free_additive R) x y z a b U;

symbol comm_ring_finite_free_weak_pullback_proj2 [R : τ CommRing]
  [x y z : τ Nat_grpd]
  [a : τ (@CommRingMatrix R y x)]
  [b : τ (@CommRingMatrix R y z)]
  (U : τ (@CommRingFiniteFreeWeakPullback R x y z a b))
  : τ (@CommRingMatrix R z (@comm_ring_finite_free_weak_pullback_rank R x y z a b U))
≔ @computational_weak_pullback_proj2
    (@CommRingFiniteFree_cat R)
    (@comm_ring_finite_free_direct_sum_func R) zero
    (@comm_ring_finite_free_additive R) x y z a b U;

// Abbreviations for the existing difference-cone/factor interfaces.
symbol CommRingFiniteFreeWeakPullbackCone [R : τ CommRing]
  [x y z : τ Nat_grpd]
  (a : τ (@CommRingMatrix R y x)) (b : τ (@CommRingMatrix R y z))
  (k : τ Nat_grpd) : Grpd
≔ @WeakPullbackCone (@CommRingFiniteFree_cat R)
    (@comm_ring_finite_free_direct_sum_func R) zero
    (@comm_ring_finite_free_additive R) x y z a b k;

symbol CommRingFiniteFreeWeakPullbackFactorOperation [R : τ CommRing]
  [x y z : τ Nat_grpd]
  (a : τ (@CommRingMatrix R y x)) (b : τ (@CommRingMatrix R y z))
  (k : τ Nat_grpd) : Grpd
≔ @WeakKernelFactorOperation (@CommRingFiniteFree_cat R)
    (@comm_ring_finite_free_preadditive R)
    (@weak_pullback_product_object (@CommRingFiniteFree_cat R)
      (@comm_ring_finite_free_direct_sum_func R) zero
      (@comm_ring_finite_free_additive R) x z) y
    (@weak_pullback_difference_fapp0 (@CommRingFiniteFree_cat R)
      (@comm_ring_finite_free_direct_sum_func R) zero
      (@comm_ring_finite_free_additive R) x y z a b) k;

symbol CommRingFiniteFreeWeakPullbackFactorLaw [R : τ CommRing]
  [x y z : τ Nat_grpd]
  [a : τ (@CommRingMatrix R y x)] [b : τ (@CommRingMatrix R y z)]
  [k : τ Nat_grpd]
  (cone : τ (@CommRingFiniteFreeWeakPullbackCone R x y z a b k))
  (factor : τ (@CommRingFiniteFreeWeakPullbackFactorOperation R x y z a b k)) : Grpd
≔ @WeakKernelFactorLaw (@CommRingFiniteFree_cat R)
    (@comm_ring_finite_free_preadditive R)
    (@weak_pullback_product_object (@CommRingFiniteFree_cat R)
      (@comm_ring_finite_free_direct_sum_func R) zero
      (@comm_ring_finite_free_additive R) x z) y
    (@weak_pullback_difference_fapp0 (@CommRingFiniteFree_cat R)
      (@comm_ring_finite_free_direct_sum_func R) zero
      (@comm_ring_finite_free_additive R) x y z a b) k
    (@weak_pullback_cone_morphism (@CommRingFiniteFree_cat R)
      (@comm_ring_finite_free_direct_sum_func R) zero
      (@comm_ring_finite_free_additive R) x y z a b k cone) factor;

// Build the existing universal owner at the supplied literal rank and cone.
symbol comm_ring_finite_free_weak_pullback_intro [R : τ CommRing]
  [x y z : τ Nat_grpd]
  [a : τ (@CommRingMatrix R y x)] [b : τ (@CommRingMatrix R y z)]
  (k : τ Nat_grpd)
  (cone : τ (@CommRingFiniteFreeWeakPullbackCone R x y z a b k))
  (factor : τ (@CommRingFiniteFreeWeakPullbackFactorOperation R x y z a b k))
  (law : τ (@CommRingFiniteFreeWeakPullbackFactorLaw R x y z a b k cone factor))
  : τ (@CommRingFiniteFreeWeakPullback R x y z a b)
≔ @computational_weak_kernel_intro (@CommRingFiniteFree_cat R)
    (@comm_ring_finite_free_preadditive R)
    (@weak_pullback_product_object (@CommRingFiniteFree_cat R)
      (@comm_ring_finite_free_direct_sum_func R) zero
      (@comm_ring_finite_free_additive R) x z) y
    (@weak_pullback_difference_fapp0 (@CommRingFiniteFree_cat R)
      (@comm_ring_finite_free_direct_sum_func R) zero
      (@comm_ring_finite_free_additive R) x y z a b) k
    (@weak_pullback_cone_morphism (@CommRingFiniteFree_cat R)
      (@comm_ring_finite_free_direct_sum_func R) zero
      (@comm_ring_finite_free_additive R) x y z a b k cone)
    (@weak_kernel_annihilator_path (@CommRingFiniteFree_cat R)
      (@comm_ring_finite_free_preadditive R)
      (@weak_pullback_product_object (@CommRingFiniteFree_cat R)
        (@comm_ring_finite_free_direct_sum_func R) zero
        (@comm_ring_finite_free_additive R) x z) y
      (@weak_pullback_difference_fapp0 (@CommRingFiniteFree_cat R)
        (@comm_ring_finite_free_direct_sum_func R) zero
        (@comm_ring_finite_free_additive R) x y z a b) k cone)
    factor law;

// A supplied equalizing pair uses original cone introduction and product beta.
symbol comm_ring_finite_free_weak_pullback_pair_cone [R : τ CommRing]
  [x y z k : τ Nat_grpd]
  [a : τ (@CommRingMatrix R y x)] [b : τ (@CommRingMatrix R y z)]
  (p : τ (@CommRingMatrix R x k)) (q : τ (@CommRingMatrix R z k))
  (compatible : τ (@= (@CommRingMatrix R y k)
    (@comp_fapp0 (@CommRingFiniteFree_cat R) k x y a p)
    (@comp_fapp0 (@CommRingFiniteFree_cat R) k z y b q)))
  : τ (@CommRingFiniteFreeWeakPullbackCone R x y z a b k)
≔ @weak_pullback_cone_intro (@CommRingFiniteFree_cat R)
    (@comm_ring_finite_free_direct_sum_func R) zero
    (@comm_ring_finite_free_additive R) x y z k a b p q compatible;
