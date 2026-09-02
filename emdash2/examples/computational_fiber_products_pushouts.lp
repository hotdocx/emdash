/* Reviewer-facing genuine computational fiber products and pushouts. */

require open emdash.emdash3_2_computational_pushouts;

// Genuine fiber-product factors are contractible, not merely selected.
assert
  (C : Cat)
  (P : τ (Functor (Product_cat C C) C))
  (t : τ (Obj C))
  (S : τ (@AdditiveCategory C P t))
  (X Y Z T : τ (Obj C))
  (alpha : τ (Hom C X Y))
  (gamma : τ (Hom C Z Y))
  (F : τ (@ComputationalFiberProduct C P t S X Y Z alpha gamma))
  (cone : τ (@FiberProductCone C P t S X Y Z alpha gamma T))
  ⊢ @computational_fiber_product_factor_contr
      C P t S X Y Z alpha gamma F T cone
  : τ (IsContr (@FiberProductFactorSpace C P t S X Y Z
      alpha gamma F T cone));

// The difference encoding derives the conventional pullback equation.
assert
  (C : Cat)
  (P : τ (Functor (Product_cat C C) C))
  (t : τ (Obj C))
  (S : τ (@AdditiveCategory C P t))
  (X Y Z : τ (Obj C))
  (alpha : τ (Hom C X Y))
  (gamma : τ (Hom C Z Y))
  (F : τ (@ComputationalFiberProduct C P t S X Y Z alpha gamma))
  ⊢ @computational_fiber_product_compatibility_path
      C P t S X Y Z alpha gamma F
  : τ (@= (Hom C
      (@computational_fiber_product_object C P t S X Y Z alpha gamma F) Y)
      (@comp_fapp0 C
        (@computational_fiber_product_object C P t S X Y Z alpha gamma F)
        X Y alpha
        (@computational_fiber_product_proj1 C P t S X Y Z alpha gamma F))
      (@comp_fapp0 C
        (@computational_fiber_product_object C P t S X Y Z alpha gamma F)
        Z Y gamma
        (@computational_fiber_product_proj2 C P t S X Y Z alpha gamma F)));

// A genuine kernel forgets coherently to the prior weak-pullback interface.
assert
  (C : Cat)
  (P : τ (Functor (Product_cat C C) C))
  (t : τ (Obj C))
  (S : τ (@AdditiveCategory C P t))
  (X Y Z : τ (Obj C))
  (alpha : τ (Hom C X Y))
  (gamma : τ (Hom C Z Y))
  (F : τ (@ComputationalFiberProduct C P t S X Y Z alpha gamma))
  ⊢ @computational_fiber_product_as_weak_pullback
      C P t S X Y Z alpha gamma F
  : τ (@ComputationalWeakPullback C P t S X Y Z alpha gamma);

// Genuine pushout cofactors are contractible.
assert
  (C : Cat)
  (P : τ (Functor (Product_cat C C) C))
  (t : τ (Obj C))
  (S : τ (@AdditiveCategory C P t))
  (X Y Z T : τ (Obj C))
  (alpha : τ (Hom C Y X))
  (gamma : τ (Hom C Y Z))
  (Q : τ (@ComputationalPushout C P t S X Y Z alpha gamma))
  (cone : τ (@PushoutCocone C P t S X Y Z alpha gamma T))
  ⊢ @computational_pushout_cofactor_contr
      C P t S X Y Z alpha gamma Q T cone
  : τ (IsContr (@PushoutCofactorSpace C P t S X Y Z
      alpha gamma Q T cone));

// A conventional compatible copair constructs the internal cocone.
assert
  (C : Cat)
  (P : τ (Functor (Product_cat C C) C))
  (t : τ (Obj C))
  (S : τ (@AdditiveCategory C P t))
  (X Y Z T : τ (Obj C))
  (alpha : τ (Hom C Y X))
  (gamma : τ (Hom C Y Z))
  (a : τ (Hom C X T))
  (b : τ (Hom C Z T))
  (p : τ (@= (Hom C Y T)
    (@comp_fapp0 C Y X T a alpha)
    (@comp_fapp0 C Y Z T b gamma)))
  ⊢ @pushout_cocone_intro C P t S X Y Z T alpha gamma a b p
  : τ (@PushoutCocone C P t S X Y Z alpha gamma T);

// The dual difference encoding derives the conventional pushout equation.
assert
  (C : Cat)
  (P : τ (Functor (Product_cat C C) C))
  (t : τ (Obj C))
  (S : τ (@AdditiveCategory C P t))
  (X Y Z : τ (Obj C))
  (alpha : τ (Hom C Y X))
  (gamma : τ (Hom C Y Z))
  (Q : τ (@ComputationalPushout C P t S X Y Z alpha gamma))
  ⊢ @computational_pushout_compatibility_path
      C P t S X Y Z alpha gamma Q
  : τ (@= (Hom C Y
      (@computational_pushout_object C P t S X Y Z alpha gamma Q))
      (@comp_fapp0 C Y X
        (@computational_pushout_object C P t S X Y Z alpha gamma Q)
        (@computational_pushout_inj1 C P t S X Y Z alpha gamma Q) alpha)
      (@comp_fapp0 C Y Z
        (@computational_pushout_object C P t S X Y Z alpha gamma Q)
        (@computational_pushout_inj2 C P t S X Y Z alpha gamma Q) gamma));

// Whole pre-Abelian capabilities select every binary construction.
assert
  (C : Cat)
  (P : τ (Functor (Product_cat C C) C))
  (t : τ (Obj C))
  (A : τ (@PreAbelianCategory C P t))
  ⊢ @computational_kernels_give_fiber_products C P t
      (@preabelian_additive C P t A)
      (@preabelian_kernels C P t A)
  : τ (@HasComputationalFiberProducts C P t
      (@preabelian_additive C P t A));

assert
  (C : Cat)
  (P : τ (Functor (Product_cat C C) C))
  (t : τ (Obj C))
  (A : τ (@PreAbelianCategory C P t))
  ⊢ @computational_cokernels_give_pushouts C P t
      (@preabelian_additive C P t A)
      (@preabelian_cokernels C P t A)
  : τ (@HasComputationalPushouts C P t
      (@preabelian_additive C P t A));
