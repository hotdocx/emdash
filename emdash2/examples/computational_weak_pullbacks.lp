/* Reviewer-facing computational weak-pullback consumers. */

require open emdash.emdash3_2_computational_weak_pullback_cones;
require open emdash.emdash3_2_commutative_algebra_finite_free_additive;

// The combined factor is reconstructed before projection.
assert
  (C : Cat)
  (P : τ (Functor (Product_cat C C) C))
  (t : τ (Obj C))
  (S : τ (@AdditiveCategory C P t))
  (X Y Z T : τ (Obj C))
  (alpha : τ (Hom C X Y))
  (gamma : τ (Hom C Z Y))
  (W : τ (@ComputationalWeakPullback C P t S X Y Z alpha gamma))
  (cone : τ (@WeakPullbackCone C P t S X Y Z alpha gamma T))
  ⊢ @computational_weak_pullback_lift_combined_path
      C P t S X Y Z alpha gamma W T cone
  : τ (@= (Hom C T (@weak_pullback_product_object C P t S X Z))
      (@comp_fapp0 C T
        (@computational_weak_pullback_object C P t S X Y Z alpha gamma W)
        (@weak_pullback_product_object C P t S X Z)
        (@computational_weak_pullback_morphism C P t S X Y Z alpha gamma W)
        (@computational_weak_pullback_lift C P t S X Y Z alpha gamma W T cone))
      (@weak_pullback_cone_morphism C P t S X Y Z alpha gamma T cone));

// Difference-zero encoding exposes the conventional equalizing equation.
assert
  (C : Cat)
  (P : τ (Functor (Product_cat C C) C))
  (t : τ (Obj C))
  (S : τ (@AdditiveCategory C P t))
  (X Y Z : τ (Obj C))
  (alpha : τ (Hom C X Y))
  (gamma : τ (Hom C Z Y))
  (W : τ (@ComputationalWeakPullback C P t S X Y Z alpha gamma))
  ⊢ @computational_weak_pullback_compatibility_path
      C P t S X Y Z alpha gamma W
  : τ (@= (Hom C
      (@computational_weak_pullback_object C P t S X Y Z alpha gamma W) Y)
      (@comp_fapp0 C
        (@computational_weak_pullback_object C P t S X Y Z alpha gamma W)
        X Y alpha
        (@computational_weak_pullback_proj1 C P t S X Y Z alpha gamma W))
      (@comp_fapp0 C
        (@computational_weak_pullback_object C P t S X Y Z alpha gamma W)
        Z Y gamma
        (@computational_weak_pullback_proj2 C P t S X Y Z alpha gamma W)));

// Conversely, an explicit equalizing pair constructs the internal cone.
assert
  (C : Cat)
  (P : τ (Functor (Product_cat C C) C))
  (t : τ (Obj C))
  (S : τ (@AdditiveCategory C P t))
  (X Y Z T : τ (Obj C))
  (alpha : τ (Hom C X Y))
  (gamma : τ (Hom C Z Y))
  (a : τ (Hom C T X))
  (b : τ (Hom C T Z))
  (p : τ (@= (Hom C T Y)
    (@comp_fapp0 C T X Y alpha a)
    (@comp_fapp0 C T Z Y gamma b)))
  ⊢ @weak_pullback_cone_intro C P t S X Y Z T alpha gamma a b p
  : τ (@WeakPullbackCone C P t S X Y Z alpha gamma T);

// Both ordinary projection equations derive from that one combined path.
assert
  (C : Cat)
  (P : τ (Functor (Product_cat C C) C))
  (t : τ (Obj C))
  (S : τ (@AdditiveCategory C P t))
  (X Y Z T : τ (Obj C))
  (alpha : τ (Hom C X Y))
  (gamma : τ (Hom C Z Y))
  (W : τ (@ComputationalWeakPullback C P t S X Y Z alpha gamma))
  (cone : τ (@WeakPullbackCone C P t S X Y Z alpha gamma T))
  ⊢ @computational_weak_pullback_lift_proj1_path
      C P t S X Y Z alpha gamma W T cone
  : τ (@= (Hom C T X)
      (@comp_fapp0 C T
        (@computational_weak_pullback_object C P t S X Y Z alpha gamma W) X
        (@computational_weak_pullback_proj1 C P t S X Y Z alpha gamma W)
        (@computational_weak_pullback_lift C P t S X Y Z alpha gamma W T cone))
      (@weak_pullback_cone_proj1 C P t S X Y Z alpha gamma T cone));

assert
  (C : Cat)
  (P : τ (Functor (Product_cat C C) C))
  (t : τ (Obj C))
  (S : τ (@AdditiveCategory C P t))
  (X Y Z T : τ (Obj C))
  (alpha : τ (Hom C X Y))
  (gamma : τ (Hom C Z Y))
  (W : τ (@ComputationalWeakPullback C P t S X Y Z alpha gamma))
  (cone : τ (@WeakPullbackCone C P t S X Y Z alpha gamma T))
  ⊢ @computational_weak_pullback_lift_proj2_path
      C P t S X Y Z alpha gamma W T cone
  : τ (@= (Hom C T Z)
      (@comp_fapp0 C T
        (@computational_weak_pullback_object C P t S X Y Z alpha gamma W) Z
        (@computational_weak_pullback_proj2 C P t S X Y Z alpha gamma W)
        (@computational_weak_pullback_lift C P t S X Y Z alpha gamma W T cone))
      (@weak_pullback_cone_proj2 C P t S X Y Z alpha gamma T cone));

// A finite-free weak-kernel capability immediately supplies all weak pullbacks.
assert
  (R : τ CommRing)
  (W : τ (@HasComputationalWeakKernels
    (@CommRingFiniteFree_cat R)
    (@comm_ring_finite_free_preadditive R)))
  ⊢ @computational_weak_kernels_give_weak_pullbacks
      (@CommRingFiniteFree_cat R)
      (@comm_ring_finite_free_direct_sum_func R)
      zero
      (@comm_ring_finite_free_additive R)
      W
  : τ (@HasComputationalWeakPullbacks
      (@CommRingFiniteFree_cat R)
      (@comm_ring_finite_free_direct_sum_func R)
      zero
      (@comm_ring_finite_free_additive R));
