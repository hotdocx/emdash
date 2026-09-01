/*
  Computational weak pullbacks derived from additive weak kernels.

  A cone is an internal annihilated arrow into X+Z for the difference map
  [alpha,-gamma]. Thus no manually stored commuting square is introduced.
  The selected weak-kernel factor is the weak-pullback lift, and ordinary
  product projections derive both reconstruction laws. Factors remain
  nonunique, exactly as required for weak pullbacks.
*/

require open emdash.emdash3_2_weak_kernels;
require open emdash.emdash3_2_additive_categories;

symbol weak_pullback_product_object
  [C : Cat]
  [P : τ (Functor (Product_cat C C) C)]
  [t : τ (Obj C)]
  (S : τ (@AdditiveCategory C P t))
  (X Z : τ (Obj C))
  : τ (Obj C)
≔ @fapp0
    (Product_cat C C) C P
    (@Product_pair C C X Z);

// Difference map [alpha,-gamma] : X+Z -> Y.
symbol weak_pullback_difference_fapp0
  [C : Cat]
  [P : τ (Functor (Product_cat C C) C)]
  [t : τ (Obj C)]
  (S : τ (@AdditiveCategory C P t))
  [X Y Z : τ (Obj C)]
  (alpha : τ (Hom C X Y))
  (gamma : τ (Hom C Z Y))
  : τ (Hom C (@weak_pullback_product_object C P t S X Z) Y)
≔ @additive_copair_fapp0 C P t S X Z Y
    alpha
    (@preadditive_hom_neg C
      (@additive_preadditive C P t S) Z Y gamma);

// A weak pullback is the selected weak kernel of [alpha,-gamma].
symbol ComputationalWeakPullback
  [C : Cat]
  [P : τ (Functor (Product_cat C C) C)]
  [t : τ (Obj C)]
  (S : τ (@AdditiveCategory C P t))
  [X Y Z : τ (Obj C)]
  (alpha : τ (Hom C X Y))
  (gamma : τ (Hom C Z Y))
  : Grpd
≔ @ComputationalWeakKernel C
    (@additive_preadditive C P t S)
    (@weak_pullback_product_object C P t S X Z) Y
    (@weak_pullback_difference_fapp0 C P t S X Y Z alpha gamma);

symbol computational_weak_pullback_of_weak_kernels
  [C : Cat]
  [P : τ (Functor (Product_cat C C) C)]
  [t : τ (Obj C)]
  (S : τ (@AdditiveCategory C P t))
  (W : τ (@HasComputationalWeakKernels C
    (@additive_preadditive C P t S)))
  [X Y Z : τ (Obj C)]
  (alpha : τ (Hom C X Y))
  (gamma : τ (Hom C Z Y))
  : τ (@ComputationalWeakPullback C P t S X Y Z alpha gamma)
≔ W
    (@weak_pullback_product_object C P t S X Z)
    Y
    (@weak_pullback_difference_fapp0 C P t S X Y Z alpha gamma);

symbol computational_weak_pullback_object
  [C : Cat]
  [P : τ (Functor (Product_cat C C) C)]
  [t : τ (Obj C)]
  [S : τ (@AdditiveCategory C P t)]
  [X Y Z : τ (Obj C)]
  [alpha : τ (Hom C X Y)]
  [gamma : τ (Hom C Z Y)]
  (W : τ (@ComputationalWeakPullback C P t S X Y Z alpha gamma))
  : τ (Obj C)
≔ @computational_weak_kernel_object C
    (@additive_preadditive C P t S)
    (@weak_pullback_product_object C P t S X Z) Y
    (@weak_pullback_difference_fapp0 C P t S X Y Z alpha gamma)
    W;

// Combined weak-pullback arrow K -> X+Z.
symbol computational_weak_pullback_morphism
  [C : Cat]
  [P : τ (Functor (Product_cat C C) C)]
  [t : τ (Obj C)]
  [S : τ (@AdditiveCategory C P t)]
  [X Y Z : τ (Obj C)]
  [alpha : τ (Hom C X Y)]
  [gamma : τ (Hom C Z Y)]
  (W : τ (@ComputationalWeakPullback C P t S X Y Z alpha gamma))
  : τ (Hom C
      (@computational_weak_pullback_object C P t S X Y Z alpha gamma W)
      (@weak_pullback_product_object C P t S X Z))
≔ @computational_weak_kernel_morphism C
    (@additive_preadditive C P t S)
    (@weak_pullback_product_object C P t S X Z) Y
    (@weak_pullback_difference_fapp0 C P t S X Y Z alpha gamma)
    W;

symbol computational_weak_pullback_proj1
  [C : Cat]
  [P : τ (Functor (Product_cat C C) C)]
  [t : τ (Obj C)]
  [S : τ (@AdditiveCategory C P t)]
  [X Y Z : τ (Obj C)]
  [alpha : τ (Hom C X Y)]
  [gamma : τ (Hom C Z Y)]
  (W : τ (@ComputationalWeakPullback C P t S X Y Z alpha gamma))
  : τ (Hom C
      (@computational_weak_pullback_object C P t S X Y Z alpha gamma W)
      X)
≔ @comp_fapp0 C
    (@computational_weak_pullback_object C P t S X Y Z alpha gamma W)
    (@weak_pullback_product_object C P t S X Z) X
    (@binary_products_proj1_fapp0 C P
      (@additive_binary_products C P t S) X Z)
    (@computational_weak_pullback_morphism C P t S X Y Z alpha gamma W);

symbol computational_weak_pullback_proj2
  [C : Cat]
  [P : τ (Functor (Product_cat C C) C)]
  [t : τ (Obj C)]
  [S : τ (@AdditiveCategory C P t)]
  [X Y Z : τ (Obj C)]
  [alpha : τ (Hom C X Y)]
  [gamma : τ (Hom C Z Y)]
  (W : τ (@ComputationalWeakPullback C P t S X Y Z alpha gamma))
  : τ (Hom C
      (@computational_weak_pullback_object C P t S X Y Z alpha gamma W)
      Z)
≔ @comp_fapp0 C
    (@computational_weak_pullback_object C P t S X Y Z alpha gamma W)
    (@weak_pullback_product_object C P t S X Z) Z
    (@binary_products_proj2_fapp0 C P
      (@additive_binary_products C P t S) X Z)
    (@computational_weak_pullback_morphism C P t S X Y Z alpha gamma W);

// Difference-map annihilation is the internal weak-pullback compatibility.
symbol computational_weak_pullback_difference_path
  [C : Cat]
  [P : τ (Functor (Product_cat C C) C)]
  [t : τ (Obj C)]
  [S : τ (@AdditiveCategory C P t)]
  [X Y Z : τ (Obj C)]
  [alpha : τ (Hom C X Y)]
  [gamma : τ (Hom C Z Y)]
  (W : τ (@ComputationalWeakPullback C P t S X Y Z alpha gamma))
  : τ (@= (Hom C
      (@computational_weak_pullback_object C P t S X Y Z alpha gamma W) Y)
      (@comp_fapp0 C
        (@computational_weak_pullback_object C P t S X Y Z alpha gamma W)
        (@weak_pullback_product_object C P t S X Z) Y
        (@weak_pullback_difference_fapp0 C P t S X Y Z alpha gamma)
        (@computational_weak_pullback_morphism C P t S X Y Z alpha gamma W))
      (@preadditive_hom_zero C
        (@additive_preadditive C P t S)
        (@computational_weak_pullback_object C P t S X Y Z alpha gamma W)
        Y))
≔ @computational_weak_kernel_annihilation C
    (@additive_preadditive C P t S)
    (@weak_pullback_product_object C P t S X Z) Y
    (@weak_pullback_difference_fapp0 C P t S X Y Z alpha gamma)
    W;

// Test cones reuse the annihilator of the difference map.
symbol WeakPullbackCone
  [C : Cat]
  [P : τ (Functor (Product_cat C C) C)]
  [t : τ (Obj C)]
  (S : τ (@AdditiveCategory C P t))
  [X Y Z : τ (Obj C)]
  (alpha : τ (Hom C X Y))
  (gamma : τ (Hom C Z Y))
  (T : τ (Obj C))
  : Grpd
≔ @WeakKernelAnnihilator C
    (@additive_preadditive C P t S)
    (@weak_pullback_product_object C P t S X Z) Y
    (@weak_pullback_difference_fapp0 C P t S X Y Z alpha gamma)
    T;

symbol weak_pullback_cone_morphism
  [C : Cat]
  [P : τ (Functor (Product_cat C C) C)]
  [t : τ (Obj C)]
  [S : τ (@AdditiveCategory C P t)]
  [X Y Z : τ (Obj C)]
  [alpha : τ (Hom C X Y)]
  [gamma : τ (Hom C Z Y)]
  [T : τ (Obj C)]
  (cone : τ (@WeakPullbackCone C P t S X Y Z alpha gamma T))
  : τ (Hom C T (@weak_pullback_product_object C P t S X Z))
≔ @weak_kernel_annihilator_arrow C
    (@additive_preadditive C P t S)
    (@weak_pullback_product_object C P t S X Z) Y
    (@weak_pullback_difference_fapp0 C P t S X Y Z alpha gamma)
    T cone;

symbol weak_pullback_cone_proj1
  [C : Cat]
  [P : τ (Functor (Product_cat C C) C)]
  [t : τ (Obj C)]
  [S : τ (@AdditiveCategory C P t)]
  [X Y Z : τ (Obj C)]
  [alpha : τ (Hom C X Y)]
  [gamma : τ (Hom C Z Y)]
  [T : τ (Obj C)]
  (cone : τ (@WeakPullbackCone C P t S X Y Z alpha gamma T))
  : τ (Hom C T X)
≔ @comp_fapp0 C T
    (@weak_pullback_product_object C P t S X Z) X
    (@binary_products_proj1_fapp0 C P
      (@additive_binary_products C P t S) X Z)
    (@weak_pullback_cone_morphism C P t S X Y Z alpha gamma T cone);

symbol weak_pullback_cone_proj2
  [C : Cat]
  [P : τ (Functor (Product_cat C C) C)]
  [t : τ (Obj C)]
  [S : τ (@AdditiveCategory C P t)]
  [X Y Z : τ (Obj C)]
  [alpha : τ (Hom C X Y)]
  [gamma : τ (Hom C Z Y)]
  [T : τ (Obj C)]
  (cone : τ (@WeakPullbackCone C P t S X Y Z alpha gamma T))
  : τ (Hom C T Z)
≔ @comp_fapp0 C T
    (@weak_pullback_product_object C P t S X Z) Z
    (@binary_products_proj2_fapp0 C P
      (@additive_binary_products C P t S) X Z)
    (@weak_pullback_cone_morphism C P t S X Y Z alpha gamma T cone);

symbol computational_weak_pullback_lift
  [C : Cat]
  [P : τ (Functor (Product_cat C C) C)]
  [t : τ (Obj C)]
  [S : τ (@AdditiveCategory C P t)]
  [X Y Z : τ (Obj C)]
  [alpha : τ (Hom C X Y)]
  [gamma : τ (Hom C Z Y)]
  (W : τ (@ComputationalWeakPullback C P t S X Y Z alpha gamma))
  (T : τ (Obj C))
  (cone : τ (@WeakPullbackCone C P t S X Y Z alpha gamma T))
  : τ (Hom C T
      (@computational_weak_pullback_object C P t S X Y Z alpha gamma W))
≔ @computational_weak_kernel_factor_fapp0 C
    (@additive_preadditive C P t S)
    (@weak_pullback_product_object C P t S X Z) Y
    (@weak_pullback_difference_fapp0 C P t S X Y Z alpha gamma)
    W T cone;

symbol computational_weak_pullback_lift_combined_path
  [C : Cat]
  [P : τ (Functor (Product_cat C C) C)]
  [t : τ (Obj C)]
  [S : τ (@AdditiveCategory C P t)]
  [X Y Z : τ (Obj C)]
  [alpha : τ (Hom C X Y)]
  [gamma : τ (Hom C Z Y)]
  (W : τ (@ComputationalWeakPullback C P t S X Y Z alpha gamma))
  (T : τ (Obj C))
  (cone : τ (@WeakPullbackCone C P t S X Y Z alpha gamma T))
  : τ (@= (Hom C T (@weak_pullback_product_object C P t S X Z))
      (@comp_fapp0 C T
        (@computational_weak_pullback_object C P t S X Y Z alpha gamma W)
        (@weak_pullback_product_object C P t S X Z)
        (@computational_weak_pullback_morphism C P t S X Y Z alpha gamma W)
        (@computational_weak_pullback_lift C P t S X Y Z alpha gamma W T cone))
      (@weak_pullback_cone_morphism C P t S X Y Z alpha gamma T cone))
≔ @computational_weak_kernel_factor_path C
    (@additive_preadditive C P t S)
    (@weak_pullback_product_object C P t S X Z) Y
    (@weak_pullback_difference_fapp0 C P t S X Y Z alpha gamma)
    W T cone;

symbol computational_weak_pullback_lift_proj1_path
  [C : Cat]
  [P : τ (Functor (Product_cat C C) C)]
  [t : τ (Obj C)]
  [S : τ (@AdditiveCategory C P t)]
  [X Y Z : τ (Obj C)]
  [alpha : τ (Hom C X Y)]
  [gamma : τ (Hom C Z Y)]
  (W : τ (@ComputationalWeakPullback C P t S X Y Z alpha gamma))
  (T : τ (Obj C))
  (cone : τ (@WeakPullbackCone C P t S X Y Z alpha gamma T))
  : τ (@= (Hom C T X)
      (@comp_fapp0 C T
        (@computational_weak_pullback_object C P t S X Y Z alpha gamma W) X
        (@computational_weak_pullback_proj1 C P t S X Y Z alpha gamma W)
        (@computational_weak_pullback_lift C P t S X Y Z alpha gamma W T cone))
      (@weak_pullback_cone_proj1 C P t S X Y Z alpha gamma T cone))
≔ @eq_trans
    (Hom C T X)
    (@comp_fapp0 C T
      (@computational_weak_pullback_object C P t S X Y Z alpha gamma W) X
      (@computational_weak_pullback_proj1 C P t S X Y Z alpha gamma W)
      (@computational_weak_pullback_lift C P t S X Y Z alpha gamma W T cone))
    (@comp_fapp0 C T
      (@weak_pullback_product_object C P t S X Z) X
      (@binary_products_proj1_fapp0 C P
        (@additive_binary_products C P t S) X Z)
      (@comp_fapp0 C T
        (@computational_weak_pullback_object C P t S X Y Z alpha gamma W)
        (@weak_pullback_product_object C P t S X Z)
        (@computational_weak_pullback_morphism C P t S X Y Z alpha gamma W)
        (@computational_weak_pullback_lift C P t S X Y Z alpha gamma W T cone)))
    (@weak_pullback_cone_proj1 C P t S X Y Z alpha gamma T cone)
    (@eq_sym (Hom C T X) _ _
      (@comp_assoc C T
        (@computational_weak_pullback_object C P t S X Y Z alpha gamma W)
        (@weak_pullback_product_object C P t S X Z) X
        (@binary_products_proj1_fapp0 C P
          (@additive_binary_products C P t S) X Z)
        (@computational_weak_pullback_morphism C P t S X Y Z alpha gamma W)
        (@computational_weak_pullback_lift C P t S X Y Z alpha gamma W T cone)))
    (@eq_ap
      (Hom C T (@weak_pullback_product_object C P t S X Z))
      (Hom C T X)
      (λ q : τ (Hom C T (@weak_pullback_product_object C P t S X Z)),
        @comp_fapp0 C T
          (@weak_pullback_product_object C P t S X Z) X
          (@binary_products_proj1_fapp0 C P
            (@additive_binary_products C P t S) X Z) q)
      _ _
      (@computational_weak_pullback_lift_combined_path
        C P t S X Y Z alpha gamma W T cone));

symbol computational_weak_pullback_lift_proj2_path
  [C : Cat]
  [P : τ (Functor (Product_cat C C) C)]
  [t : τ (Obj C)]
  [S : τ (@AdditiveCategory C P t)]
  [X Y Z : τ (Obj C)]
  [alpha : τ (Hom C X Y)]
  [gamma : τ (Hom C Z Y)]
  (W : τ (@ComputationalWeakPullback C P t S X Y Z alpha gamma))
  (T : τ (Obj C))
  (cone : τ (@WeakPullbackCone C P t S X Y Z alpha gamma T))
  : τ (@= (Hom C T Z)
      (@comp_fapp0 C T
        (@computational_weak_pullback_object C P t S X Y Z alpha gamma W) Z
        (@computational_weak_pullback_proj2 C P t S X Y Z alpha gamma W)
        (@computational_weak_pullback_lift C P t S X Y Z alpha gamma W T cone))
      (@weak_pullback_cone_proj2 C P t S X Y Z alpha gamma T cone))
≔ @eq_trans
    (Hom C T Z)
    (@comp_fapp0 C T
      (@computational_weak_pullback_object C P t S X Y Z alpha gamma W) Z
      (@computational_weak_pullback_proj2 C P t S X Y Z alpha gamma W)
      (@computational_weak_pullback_lift C P t S X Y Z alpha gamma W T cone))
    (@comp_fapp0 C T
      (@weak_pullback_product_object C P t S X Z) Z
      (@binary_products_proj2_fapp0 C P
        (@additive_binary_products C P t S) X Z)
      (@comp_fapp0 C T
        (@computational_weak_pullback_object C P t S X Y Z alpha gamma W)
        (@weak_pullback_product_object C P t S X Z)
        (@computational_weak_pullback_morphism C P t S X Y Z alpha gamma W)
        (@computational_weak_pullback_lift C P t S X Y Z alpha gamma W T cone)))
    (@weak_pullback_cone_proj2 C P t S X Y Z alpha gamma T cone)
    (@eq_sym (Hom C T Z) _ _
      (@comp_assoc C T
        (@computational_weak_pullback_object C P t S X Y Z alpha gamma W)
        (@weak_pullback_product_object C P t S X Z) Z
        (@binary_products_proj2_fapp0 C P
          (@additive_binary_products C P t S) X Z)
        (@computational_weak_pullback_morphism C P t S X Y Z alpha gamma W)
        (@computational_weak_pullback_lift C P t S X Y Z alpha gamma W T cone)))
    (@eq_ap
      (Hom C T (@weak_pullback_product_object C P t S X Z))
      (Hom C T Z)
      (λ q : τ (Hom C T (@weak_pullback_product_object C P t S X Z)),
        @comp_fapp0 C T
          (@weak_pullback_product_object C P t S X Z) Z
          (@binary_products_proj2_fapp0 C P
            (@additive_binary_products C P t S) X Z) q)
      _ _
      (@computational_weak_pullback_lift_combined_path
        C P t S X Y Z alpha gamma W T cone));

symbol HasComputationalWeakPullbacks
  [C : Cat]
  [P : τ (Functor (Product_cat C C) C)]
  [t : τ (Obj C)]
  (S : τ (@AdditiveCategory C P t))
  : Grpd
≔ @Pi_grpd (Obj C) (λ X : τ (Obj C),
    @Pi_grpd (Obj C) (λ Y : τ (Obj C),
      @Pi_grpd (Obj C) (λ Z : τ (Obj C),
        @Pi_grpd (Hom C X Y) (λ alpha : τ (Hom C X Y),
          @Pi_grpd (Hom C Z Y) (λ gamma : τ (Hom C Z Y),
            @ComputationalWeakPullback C P t S X Y Z alpha gamma)))));

symbol computational_weak_kernels_give_weak_pullbacks
  [C : Cat]
  [P : τ (Functor (Product_cat C C) C)]
  [t : τ (Obj C)]
  (S : τ (@AdditiveCategory C P t))
  (W : τ (@HasComputationalWeakKernels C
    (@additive_preadditive C P t S)))
  : τ (@HasComputationalWeakPullbacks C P t S)
≔ λ X : τ (Obj C), λ Y : τ (Obj C), λ Z : τ (Obj C),
    λ alpha : τ (Hom C X Y), λ gamma : τ (Hom C Z Y),
      @computational_weak_pullback_of_weak_kernels
        C P t S W X Y Z alpha gamma;
