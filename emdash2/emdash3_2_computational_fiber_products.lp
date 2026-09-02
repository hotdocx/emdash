/*
  Genuine computational fiber products from additive biproducts and kernels.

  The primary cone remains the existing annihilator HFiber for [alpha,-gamma].
  Replacing its weak kernel by a genuine kernel makes every factor space
  contractible. Conventional equalizing pairs reuse the existing additive
  cone adapter; no manually stored square or runtime rule is introduced.
*/

require open emdash.emdash3_2_computational_weak_pullback_cones;
require open emdash.emdash3_2_kernels_cokernels;

// Every genuine kernel supplies the corresponding selected weak kernel.
symbol computational_kernel_as_weak_kernel
  [C : Cat]
  [S : τ (@PreadditiveCategory C)]
  [A B : τ (Obj C)]
  [alpha : τ (Hom C A B)]
  (K : τ (@ComputationalKernel C S A B alpha))
  : τ (@ComputationalWeakKernel C S A B alpha)
≔ @computational_weak_kernel_intro C S A B alpha
    (@computational_kernel_object C S A B alpha K)
    (@computational_kernel_morphism C S A B alpha K)
    (@computational_kernel_annihilation C S A B alpha K)
    (λ T : τ (Obj C),
      λ cone : τ (@WeakKernelAnnihilator C S A B alpha T),
        @computational_kernel_lift C S A B alpha K T cone)
    (λ T : τ (Obj C),
      λ cone : τ (@WeakKernelAnnihilator C S A B alpha T),
        @computational_kernel_lift_path C S A B alpha K T cone);

// The genuine fiber product is Ker([alpha,-gamma]).
symbol ComputationalFiberProduct
  [C : Cat]
  [P : τ (Functor (Product_cat C C) C)]
  [t : τ (Obj C)]
  (S : τ (@AdditiveCategory C P t))
  [X Y Z : τ (Obj C)]
  (alpha : τ (Hom C X Y))
  (gamma : τ (Hom C Z Y))
  : Grpd
≔ @ComputationalKernel C
    (@additive_preadditive C P t S)
    (@weak_pullback_product_object C P t S X Z) Y
    (@weak_pullback_difference_fapp0 C P t S X Y Z alpha gamma);

symbol computational_fiber_product_of_kernels
  [C : Cat]
  [P : τ (Functor (Product_cat C C) C)]
  [t : τ (Obj C)]
  (S : τ (@AdditiveCategory C P t))
  (K : τ (@HasComputationalKernels C
    (@additive_preadditive C P t S)))
  [X Y Z : τ (Obj C)]
  (alpha : τ (Hom C X Y))
  (gamma : τ (Hom C Z Y))
  : τ (@ComputationalFiberProduct C P t S X Y Z alpha gamma)
≔ K
    (@weak_pullback_product_object C P t S X Z)
    Y
    (@weak_pullback_difference_fapp0 C P t S X Y Z alpha gamma);

// Forgetting uniqueness recovers the existing computational weak pullback.
symbol computational_fiber_product_as_weak_pullback
  [C : Cat]
  [P : τ (Functor (Product_cat C C) C)]
  [t : τ (Obj C)]
  [S : τ (@AdditiveCategory C P t)]
  [X Y Z : τ (Obj C)]
  [alpha : τ (Hom C X Y)]
  [gamma : τ (Hom C Z Y)]
  (F : τ (@ComputationalFiberProduct C P t S X Y Z alpha gamma))
  : τ (@ComputationalWeakPullback C P t S X Y Z alpha gamma)
≔ @computational_kernel_as_weak_kernel C
    (@additive_preadditive C P t S)
    (@weak_pullback_product_object C P t S X Z) Y
    (@weak_pullback_difference_fapp0 C P t S X Y Z alpha gamma)
    F;

symbol computational_fiber_product_object
  [C : Cat]
  [P : τ (Functor (Product_cat C C) C)]
  [t : τ (Obj C)]
  [S : τ (@AdditiveCategory C P t)]
  [X Y Z : τ (Obj C)]
  [alpha : τ (Hom C X Y)]
  [gamma : τ (Hom C Z Y)]
  (F : τ (@ComputationalFiberProduct C P t S X Y Z alpha gamma))
  : τ (Obj C)
≔ @computational_kernel_object C
    (@additive_preadditive C P t S)
    (@weak_pullback_product_object C P t S X Z) Y
    (@weak_pullback_difference_fapp0 C P t S X Y Z alpha gamma)
    F;

symbol computational_fiber_product_morphism
  [C : Cat]
  [P : τ (Functor (Product_cat C C) C)]
  [t : τ (Obj C)]
  [S : τ (@AdditiveCategory C P t)]
  [X Y Z : τ (Obj C)]
  [alpha : τ (Hom C X Y)]
  [gamma : τ (Hom C Z Y)]
  (F : τ (@ComputationalFiberProduct C P t S X Y Z alpha gamma))
  : τ (Hom C
      (@computational_fiber_product_object C P t S X Y Z alpha gamma F)
      (@weak_pullback_product_object C P t S X Z))
≔ @computational_kernel_morphism C
    (@additive_preadditive C P t S)
    (@weak_pullback_product_object C P t S X Z) Y
    (@weak_pullback_difference_fapp0 C P t S X Y Z alpha gamma)
    F;

symbol computational_fiber_product_proj1
  [C : Cat]
  [P : τ (Functor (Product_cat C C) C)]
  [t : τ (Obj C)]
  [S : τ (@AdditiveCategory C P t)]
  [X Y Z : τ (Obj C)]
  [alpha : τ (Hom C X Y)]
  [gamma : τ (Hom C Z Y)]
  (F : τ (@ComputationalFiberProduct C P t S X Y Z alpha gamma))
  : τ (Hom C
      (@computational_fiber_product_object C P t S X Y Z alpha gamma F) X)
≔ @comp_fapp0 C
    (@computational_fiber_product_object C P t S X Y Z alpha gamma F)
    (@weak_pullback_product_object C P t S X Z) X
    (@binary_products_proj1_fapp0 C P
      (@additive_binary_products C P t S) X Z)
    (@computational_fiber_product_morphism C P t S X Y Z alpha gamma F);

symbol computational_fiber_product_proj2
  [C : Cat]
  [P : τ (Functor (Product_cat C C) C)]
  [t : τ (Obj C)]
  [S : τ (@AdditiveCategory C P t)]
  [X Y Z : τ (Obj C)]
  [alpha : τ (Hom C X Y)]
  [gamma : τ (Hom C Z Y)]
  (F : τ (@ComputationalFiberProduct C P t S X Y Z alpha gamma))
  : τ (Hom C
      (@computational_fiber_product_object C P t S X Y Z alpha gamma F) Z)
≔ @comp_fapp0 C
    (@computational_fiber_product_object C P t S X Y Z alpha gamma F)
    (@weak_pullback_product_object C P t S X Z) Z
    (@binary_products_proj2_fapp0 C P
      (@additive_binary_products C P t S) X Z)
    (@computational_fiber_product_morphism C P t S X Y Z alpha gamma F);

// Primary cones are exactly the existing difference-annihilator fibres.
symbol FiberProductCone
  [C : Cat]
  [P : τ (Functor (Product_cat C C) C)]
  [t : τ (Obj C)]
  (S : τ (@AdditiveCategory C P t))
  [X Y Z : τ (Obj C)]
  (alpha : τ (Hom C X Y))
  (gamma : τ (Hom C Z Y))
  (T : τ (Obj C))
  : Grpd
≔ @WeakPullbackCone C P t S X Y Z alpha gamma T;

// Factor space inherited definitionally from the selected genuine kernel.
symbol FiberProductFactorSpace
  [C : Cat]
  [P : τ (Functor (Product_cat C C) C)]
  [t : τ (Obj C)]
  [S : τ (@AdditiveCategory C P t)]
  [X Y Z : τ (Obj C)]
  [alpha : τ (Hom C X Y)]
  [gamma : τ (Hom C Z Y)]
  (F : τ (@ComputationalFiberProduct C P t S X Y Z alpha gamma))
  (T : τ (Obj C))
  (cone : τ (@FiberProductCone C P t S X Y Z alpha gamma T))
  : Grpd
≔ @KernelFactorSpace C
    (@additive_preadditive C P t S)
    (@weak_pullback_product_object C P t S X Z) Y
    (@weak_pullback_difference_fapp0 C P t S X Y Z alpha gamma)
    (@computational_fiber_product_object C P t S X Y Z alpha gamma F)
    (@computational_fiber_product_morphism C P t S X Y Z alpha gamma F)
    T cone;

symbol computational_fiber_product_factor_contr
  [C : Cat]
  [P : τ (Functor (Product_cat C C) C)]
  [t : τ (Obj C)]
  [S : τ (@AdditiveCategory C P t)]
  [X Y Z : τ (Obj C)]
  [alpha : τ (Hom C X Y)]
  [gamma : τ (Hom C Z Y)]
  (F : τ (@ComputationalFiberProduct C P t S X Y Z alpha gamma))
  (T : τ (Obj C))
  (cone : τ (@FiberProductCone C P t S X Y Z alpha gamma T))
  : τ (IsContr (@FiberProductFactorSpace C P t S X Y Z
      alpha gamma F T cone))
≔ @computational_kernel_factor_contr C
    (@additive_preadditive C P t S)
    (@weak_pullback_product_object C P t S X Z) Y
    (@weak_pullback_difference_fapp0 C P t S X Y Z alpha gamma)
    F T cone;

symbol computational_fiber_product_lift
  [C : Cat]
  [P : τ (Functor (Product_cat C C) C)]
  [t : τ (Obj C)]
  [S : τ (@AdditiveCategory C P t)]
  [X Y Z : τ (Obj C)]
  [alpha : τ (Hom C X Y)]
  [gamma : τ (Hom C Z Y)]
  (F : τ (@ComputationalFiberProduct C P t S X Y Z alpha gamma))
  (T : τ (Obj C))
  (cone : τ (@FiberProductCone C P t S X Y Z alpha gamma T))
  : τ (Hom C T
      (@computational_fiber_product_object C P t S X Y Z alpha gamma F))
≔ @computational_kernel_lift C
    (@additive_preadditive C P t S)
    (@weak_pullback_product_object C P t S X Z) Y
    (@weak_pullback_difference_fapp0 C P t S X Y Z alpha gamma)
    F T cone;

symbol computational_fiber_product_lift_combined_path
  [C : Cat]
  [P : τ (Functor (Product_cat C C) C)]
  [t : τ (Obj C)]
  [S : τ (@AdditiveCategory C P t)]
  [X Y Z : τ (Obj C)]
  [alpha : τ (Hom C X Y)]
  [gamma : τ (Hom C Z Y)]
  (F : τ (@ComputationalFiberProduct C P t S X Y Z alpha gamma))
  (T : τ (Obj C))
  (cone : τ (@FiberProductCone C P t S X Y Z alpha gamma T))
  : τ (@= (Hom C T (@weak_pullback_product_object C P t S X Z))
      (@comp_fapp0 C T
        (@computational_fiber_product_object C P t S X Y Z alpha gamma F)
        (@weak_pullback_product_object C P t S X Z)
        (@computational_fiber_product_morphism C P t S X Y Z alpha gamma F)
        (@computational_fiber_product_lift C P t S X Y Z alpha gamma F T cone))
      (@weak_pullback_cone_morphism C P t S X Y Z alpha gamma T cone))
≔ @computational_kernel_lift_path C
    (@additive_preadditive C P t S)
    (@weak_pullback_product_object C P t S X Z) Y
    (@weak_pullback_difference_fapp0 C P t S X Y Z alpha gamma)
    F T cone;

symbol computational_fiber_product_lift_proj1_path
  [C : Cat]
  [P : τ (Functor (Product_cat C C) C)]
  [t : τ (Obj C)]
  [S : τ (@AdditiveCategory C P t)]
  [X Y Z : τ (Obj C)]
  [alpha : τ (Hom C X Y)]
  [gamma : τ (Hom C Z Y)]
  (F : τ (@ComputationalFiberProduct C P t S X Y Z alpha gamma))
  (T : τ (Obj C))
  (cone : τ (@FiberProductCone C P t S X Y Z alpha gamma T))
  : τ (@= (Hom C T X)
      (@comp_fapp0 C T
        (@computational_fiber_product_object C P t S X Y Z alpha gamma F) X
        (@computational_fiber_product_proj1 C P t S X Y Z alpha gamma F)
        (@computational_fiber_product_lift C P t S X Y Z alpha gamma F T cone))
      (@weak_pullback_cone_proj1 C P t S X Y Z alpha gamma T cone))
≔ @computational_weak_pullback_lift_proj1_path C P t S
    X Y Z alpha gamma
    (@computational_fiber_product_as_weak_pullback C P t S
      X Y Z alpha gamma F)
    T cone;

symbol computational_fiber_product_lift_proj2_path
  [C : Cat]
  [P : τ (Functor (Product_cat C C) C)]
  [t : τ (Obj C)]
  [S : τ (@AdditiveCategory C P t)]
  [X Y Z : τ (Obj C)]
  [alpha : τ (Hom C X Y)]
  [gamma : τ (Hom C Z Y)]
  (F : τ (@ComputationalFiberProduct C P t S X Y Z alpha gamma))
  (T : τ (Obj C))
  (cone : τ (@FiberProductCone C P t S X Y Z alpha gamma T))
  : τ (@= (Hom C T Z)
      (@comp_fapp0 C T
        (@computational_fiber_product_object C P t S X Y Z alpha gamma F) Z
        (@computational_fiber_product_proj2 C P t S X Y Z alpha gamma F)
        (@computational_fiber_product_lift C P t S X Y Z alpha gamma F T cone))
      (@weak_pullback_cone_proj2 C P t S X Y Z alpha gamma T cone))
≔ @computational_weak_pullback_lift_proj2_path C P t S
    X Y Z alpha gamma
    (@computational_fiber_product_as_weak_pullback C P t S
      X Y Z alpha gamma F)
    T cone;

symbol computational_fiber_product_lift_unique_path
  [C : Cat]
  [P : τ (Functor (Product_cat C C) C)]
  [t : τ (Obj C)]
  [S : τ (@AdditiveCategory C P t)]
  [X Y Z : τ (Obj C)]
  [alpha : τ (Hom C X Y)]
  [gamma : τ (Hom C Z Y)]
  (F : τ (@ComputationalFiberProduct C P t S X Y Z alpha gamma))
  (T : τ (Obj C))
  (cone : τ (@FiberProductCone C P t S X Y Z alpha gamma T))
  (u : τ (Hom C T
    (@computational_fiber_product_object C P t S X Y Z alpha gamma F)))
  (p : τ (@= (Hom C T (@weak_pullback_product_object C P t S X Z))
    (@comp_fapp0 C T
      (@computational_fiber_product_object C P t S X Y Z alpha gamma F)
      (@weak_pullback_product_object C P t S X Z)
      (@computational_fiber_product_morphism C P t S X Y Z alpha gamma F) u)
    (@weak_pullback_cone_morphism C P t S X Y Z alpha gamma T cone)))
  : τ (@= (Hom C T
      (@computational_fiber_product_object C P t S X Y Z alpha gamma F))
      (@computational_fiber_product_lift C P t S X Y Z alpha gamma F T cone)
      u)
≔ @computational_kernel_lift_unique_path C
    (@additive_preadditive C P t S)
    (@weak_pullback_product_object C P t S X Z) Y
    (@weak_pullback_difference_fapp0 C P t S X Y Z alpha gamma)
    F T cone u p;

// Ordinary compatibility is inherited through the weak-pullback view.
symbol computational_fiber_product_compatibility_path
  [C : Cat]
  [P : τ (Functor (Product_cat C C) C)]
  [t : τ (Obj C)]
  [S : τ (@AdditiveCategory C P t)]
  [X Y Z : τ (Obj C)]
  [alpha : τ (Hom C X Y)]
  [gamma : τ (Hom C Z Y)]
  (F : τ (@ComputationalFiberProduct C P t S X Y Z alpha gamma))
  : τ (@= (Hom C
      (@computational_fiber_product_object C P t S X Y Z alpha gamma F) Y)
      (@comp_fapp0 C
        (@computational_fiber_product_object C P t S X Y Z alpha gamma F)
        X Y alpha
        (@computational_fiber_product_proj1 C P t S X Y Z alpha gamma F))
      (@comp_fapp0 C
        (@computational_fiber_product_object C P t S X Y Z alpha gamma F)
        Z Y gamma
        (@computational_fiber_product_proj2 C P t S X Y Z alpha gamma F)))
≔ @computational_weak_pullback_compatibility_path C P t S
    X Y Z alpha gamma
    (@computational_fiber_product_as_weak_pullback C P t S
      X Y Z alpha gamma F);

// A conventional compatible pair is converted into the primary HFiber cone.
symbol fiber_product_cone_intro
  [C : Cat]
  [P : τ (Functor (Product_cat C C) C)]
  [t : τ (Obj C)]
  [S : τ (@AdditiveCategory C P t)]
  [X Y Z T : τ (Obj C)]
  (alpha : τ (Hom C X Y))
  (gamma : τ (Hom C Z Y))
  (a : τ (Hom C T X))
  (b : τ (Hom C T Z))
  (compatibility : τ (@= (Hom C T Y)
    (@comp_fapp0 C T X Y alpha a)
    (@comp_fapp0 C T Z Y gamma b)))
  : τ (@FiberProductCone C P t S X Y Z alpha gamma T)
≔ @weak_pullback_cone_intro C P t S X Y Z T
    alpha gamma a b compatibility;

symbol HasComputationalFiberProducts
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
            @ComputationalFiberProduct C P t S X Y Z alpha gamma)))));

symbol computational_kernels_give_fiber_products
  [C : Cat]
  [P : τ (Functor (Product_cat C C) C)]
  [t : τ (Obj C)]
  (S : τ (@AdditiveCategory C P t))
  (K : τ (@HasComputationalKernels C
    (@additive_preadditive C P t S)))
  : τ (@HasComputationalFiberProducts C P t S)
≔ λ X : τ (Obj C), λ Y : τ (Obj C), λ Z : τ (Obj C),
    λ alpha : τ (Hom C X Y), λ gamma : τ (Hom C Z Y),
      @computational_fiber_product_of_kernels C P t S K
        X Y Z alpha gamma;
