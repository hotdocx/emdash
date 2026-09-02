/*
  Genuine computational pushouts from additive biproducts and cokernels.

  A cocone is the existing coannihilator HFiber for the difference
  iota_1 o alpha + iota_2 o (-gamma). Its selected cokernel makes every
  cofactor space contractible. No manual square or runtime rule is added.
*/

require open emdash.emdash3_2_computational_fiber_products;

symbol pushout_product_object
  [C : Cat]
  [P : τ (Functor (Product_cat C C) C)]
  [t : τ (Obj C)]
  (S : τ (@AdditiveCategory C P t))
  (X Z : τ (Obj C))
  : τ (Obj C)
≔ @fapp0 (Product_cat C C) C P (@Product_pair C C X Z);

// Difference map <alpha,-gamma> : Y -> X+Z.
symbol pushout_difference_fapp0
  [C : Cat]
  [P : τ (Functor (Product_cat C C) C)]
  [t : τ (Obj C)]
  (S : τ (@AdditiveCategory C P t))
  [X Y Z : τ (Obj C)]
  (alpha : τ (Hom C Y X))
  (gamma : τ (Hom C Y Z))
  : τ (Hom C Y (@pushout_product_object C P t S X Z))
≔ @preadditive_hom_add C
    (@additive_preadditive C P t S) Y
    (@pushout_product_object C P t S X Z)
    (@comp_fapp0 C Y X
      (@pushout_product_object C P t S X Z)
      (@additive_inj1_fapp0 C P t S X Z) alpha)
    (@comp_fapp0 C Y Z
      (@pushout_product_object C P t S X Z)
      (@additive_inj2_fapp0 C P t S X Z)
      (@preadditive_hom_neg C
        (@additive_preadditive C P t S) Y Z gamma));

// The genuine pushout is Coker(<alpha,-gamma>).
symbol ComputationalPushout
  [C : Cat]
  [P : τ (Functor (Product_cat C C) C)]
  [t : τ (Obj C)]
  (S : τ (@AdditiveCategory C P t))
  [X Y Z : τ (Obj C)]
  (alpha : τ (Hom C Y X))
  (gamma : τ (Hom C Y Z))
  : Grpd
≔ @ComputationalCokernel C
    (@additive_preadditive C P t S)
    Y (@pushout_product_object C P t S X Z)
    (@pushout_difference_fapp0 C P t S X Y Z alpha gamma);

symbol computational_pushout_of_cokernels
  [C : Cat]
  [P : τ (Functor (Product_cat C C) C)]
  [t : τ (Obj C)]
  (S : τ (@AdditiveCategory C P t))
  (Q : τ (@HasComputationalCokernels C
    (@additive_preadditive C P t S)))
  [X Y Z : τ (Obj C)]
  (alpha : τ (Hom C Y X))
  (gamma : τ (Hom C Y Z))
  : τ (@ComputationalPushout C P t S X Y Z alpha gamma)
≔ Q Y
    (@pushout_product_object C P t S X Z)
    (@pushout_difference_fapp0 C P t S X Y Z alpha gamma);

symbol computational_pushout_object
  [C : Cat]
  [P : τ (Functor (Product_cat C C) C)]
  [t : τ (Obj C)]
  [S : τ (@AdditiveCategory C P t)]
  [X Y Z : τ (Obj C)]
  [alpha : τ (Hom C Y X)]
  [gamma : τ (Hom C Y Z)]
  (Q : τ (@ComputationalPushout C P t S X Y Z alpha gamma))
  : τ (Obj C)
≔ @computational_cokernel_object C
    (@additive_preadditive C P t S)
    Y (@pushout_product_object C P t S X Z)
    (@pushout_difference_fapp0 C P t S X Y Z alpha gamma) Q;

symbol computational_pushout_morphism
  [C : Cat]
  [P : τ (Functor (Product_cat C C) C)]
  [t : τ (Obj C)]
  [S : τ (@AdditiveCategory C P t)]
  [X Y Z : τ (Obj C)]
  [alpha : τ (Hom C Y X)]
  [gamma : τ (Hom C Y Z)]
  (Q : τ (@ComputationalPushout C P t S X Y Z alpha gamma))
  : τ (Hom C
      (@pushout_product_object C P t S X Z)
      (@computational_pushout_object C P t S X Y Z alpha gamma Q))
≔ @computational_cokernel_morphism C
    (@additive_preadditive C P t S)
    Y (@pushout_product_object C P t S X Z)
    (@pushout_difference_fapp0 C P t S X Y Z alpha gamma) Q;

symbol computational_pushout_inj1
  [C : Cat]
  [P : τ (Functor (Product_cat C C) C)]
  [t : τ (Obj C)]
  [S : τ (@AdditiveCategory C P t)]
  [X Y Z : τ (Obj C)]
  [alpha : τ (Hom C Y X)]
  [gamma : τ (Hom C Y Z)]
  (Q : τ (@ComputationalPushout C P t S X Y Z alpha gamma))
  : τ (Hom C X
      (@computational_pushout_object C P t S X Y Z alpha gamma Q))
≔ @comp_fapp0 C X
    (@pushout_product_object C P t S X Z)
    (@computational_pushout_object C P t S X Y Z alpha gamma Q)
    (@computational_pushout_morphism C P t S X Y Z alpha gamma Q)
    (@additive_inj1_fapp0 C P t S X Z);

symbol computational_pushout_inj2
  [C : Cat]
  [P : τ (Functor (Product_cat C C) C)]
  [t : τ (Obj C)]
  [S : τ (@AdditiveCategory C P t)]
  [X Y Z : τ (Obj C)]
  [alpha : τ (Hom C Y X)]
  [gamma : τ (Hom C Y Z)]
  (Q : τ (@ComputationalPushout C P t S X Y Z alpha gamma))
  : τ (Hom C Z
      (@computational_pushout_object C P t S X Y Z alpha gamma Q))
≔ @comp_fapp0 C Z
    (@pushout_product_object C P t S X Z)
    (@computational_pushout_object C P t S X Y Z alpha gamma Q)
    (@computational_pushout_morphism C P t S X Y Z alpha gamma Q)
    (@additive_inj2_fapp0 C P t S X Z);

// Postcomposition also preserves additive inverses.
symbol preadditive_comp_neg_right_path
  [C : Cat]
  (S : τ (@PreadditiveCategory C))
  [X Y Z : τ (Obj C)]
  (g : τ (Hom C Y Z))
  (f : τ (Hom C X Y))
  : τ (@= (Hom C X Z)
      (@comp_fapp0 C X Y Z g
        (@preadditive_hom_neg C S X Y f))
      (@preadditive_hom_neg C S X Z
        (@comp_fapp0 C X Y Z g f)))
≔ @abelian_group_add_inverse_unique_path
    (Hom C X Z)
    (@preadditive_hom_structure C S X Z)
    (@comp_fapp0 C X Y Z g f)
    (@comp_fapp0 C X Y Z g
      (@preadditive_hom_neg C S X Y f))
    (@eq_trans (Hom C X Z) _ _ _
      (@eq_sym (Hom C X Z) _ _
        ((@preadditive_comp_add_right_law C S)
          X Y Z g f (@preadditive_hom_neg C S X Y f)))
      (@eq_trans (Hom C X Z) _ _ _
        (@eq_ap (Hom C X Y) (Hom C X Z)
          (λ q : τ (Hom C X Y), @comp_fapp0 C X Y Z g q)
          (@preadditive_hom_add C S X Y f
            (@preadditive_hom_neg C S X Y f))
          (@preadditive_hom_zero C S X Y)
          ((@abelian_group_add_inv_law
            (Hom C X Y)
            (@preadditive_hom_structure C S X Y)) f))
        (@preadditive_comp_zero_right_path C S X Y Z g)));

// Expand q o <alpha,-gamma> into q iota_1 alpha - q iota_2 gamma.
symbol computational_pushout_difference_expansion_path
  [C : Cat]
  [P : τ (Functor (Product_cat C C) C)]
  [t : τ (Obj C)]
  [S : τ (@AdditiveCategory C P t)]
  [X Y Z : τ (Obj C)]
  [alpha : τ (Hom C Y X)]
  [gamma : τ (Hom C Y Z)]
  (Q : τ (@ComputationalPushout C P t S X Y Z alpha gamma))
  : τ (@= (Hom C Y
      (@computational_pushout_object C P t S X Y Z alpha gamma Q))
      (@comp_fapp0 C Y
        (@pushout_product_object C P t S X Z)
        (@computational_pushout_object C P t S X Y Z alpha gamma Q)
        (@computational_pushout_morphism C P t S X Y Z alpha gamma Q)
        (@pushout_difference_fapp0 C P t S X Y Z alpha gamma))
      (@preadditive_hom_add C
        (@additive_preadditive C P t S) Y
        (@computational_pushout_object C P t S X Y Z alpha gamma Q)
        (@comp_fapp0 C Y X
          (@computational_pushout_object C P t S X Y Z alpha gamma Q)
          (@computational_pushout_inj1 C P t S X Y Z alpha gamma Q) alpha)
        (@preadditive_hom_neg C
          (@additive_preadditive C P t S) Y
          (@computational_pushout_object C P t S X Y Z alpha gamma Q)
          (@comp_fapp0 C Y Z
            (@computational_pushout_object C P t S X Y Z alpha gamma Q)
            (@computational_pushout_inj2 C P t S X Y Z alpha gamma Q) gamma))))
≔ @eq_trans _ _
    (@preadditive_hom_add C
      (@additive_preadditive C P t S) Y
      (@computational_pushout_object C P t S X Y Z alpha gamma Q)
      (@comp_fapp0 C Y
        (@pushout_product_object C P t S X Z)
        (@computational_pushout_object C P t S X Y Z alpha gamma Q)
        (@computational_pushout_morphism C P t S X Y Z alpha gamma Q)
        (@comp_fapp0 C Y X
          (@pushout_product_object C P t S X Z)
          (@additive_inj1_fapp0 C P t S X Z) alpha))
      (@comp_fapp0 C Y
        (@pushout_product_object C P t S X Z)
        (@computational_pushout_object C P t S X Y Z alpha gamma Q)
        (@computational_pushout_morphism C P t S X Y Z alpha gamma Q)
        (@comp_fapp0 C Y Z
          (@pushout_product_object C P t S X Z)
          (@additive_inj2_fapp0 C P t S X Z)
          (@preadditive_hom_neg C
            (@additive_preadditive C P t S) Y Z gamma))))
    _
    ((@preadditive_comp_add_right_law C
      (@additive_preadditive C P t S))
      Y (@pushout_product_object C P t S X Z)
      (@computational_pushout_object C P t S X Y Z alpha gamma Q)
      (@computational_pushout_morphism C P t S X Y Z alpha gamma Q)
      (@comp_fapp0 C Y X
        (@pushout_product_object C P t S X Z)
        (@additive_inj1_fapp0 C P t S X Z) alpha)
      (@comp_fapp0 C Y Z
        (@pushout_product_object C P t S X Z)
        (@additive_inj2_fapp0 C P t S X Z)
        (@preadditive_hom_neg C
          (@additive_preadditive C P t S) Y Z gamma)))
    (@additive_add_congr_path C P t S Y
      (@computational_pushout_object C P t S X Y Z alpha gamma Q)
      _ _ _ _
      (@comp_assoc C Y X
        (@pushout_product_object C P t S X Z)
        (@computational_pushout_object C P t S X Y Z alpha gamma Q)
        (@computational_pushout_morphism C P t S X Y Z alpha gamma Q)
        (@additive_inj1_fapp0 C P t S X Z) alpha)
      (@eq_trans _ _
        (@comp_fapp0 C Y Z
          (@computational_pushout_object C P t S X Y Z alpha gamma Q)
          (@computational_pushout_inj2 C P t S X Y Z alpha gamma Q)
          (@preadditive_hom_neg C
            (@additive_preadditive C P t S) Y Z gamma))
        _
        (@comp_assoc C Y Z
          (@pushout_product_object C P t S X Z)
          (@computational_pushout_object C P t S X Y Z alpha gamma Q)
          (@computational_pushout_morphism C P t S X Y Z alpha gamma Q)
          (@additive_inj2_fapp0 C P t S X Z)
          (@preadditive_hom_neg C
            (@additive_preadditive C P t S) Y Z gamma))
        (@preadditive_comp_neg_right_path C
          (@additive_preadditive C P t S) Y Z
          (@computational_pushout_object C P t S X Y Z alpha gamma Q)
          (@computational_pushout_inj2 C P t S X Y Z alpha gamma Q) gamma)));

symbol computational_pushout_compatibility_path
  [C : Cat]
  [P : τ (Functor (Product_cat C C) C)]
  [t : τ (Obj C)]
  [S : τ (@AdditiveCategory C P t)]
  [X Y Z : τ (Obj C)]
  [alpha : τ (Hom C Y X)]
  [gamma : τ (Hom C Y Z)]
  (Q : τ (@ComputationalPushout C P t S X Y Z alpha gamma))
  : τ (@= (Hom C Y
      (@computational_pushout_object C P t S X Y Z alpha gamma Q))
      (@comp_fapp0 C Y X
        (@computational_pushout_object C P t S X Y Z alpha gamma Q)
        (@computational_pushout_inj1 C P t S X Y Z alpha gamma Q) alpha)
      (@comp_fapp0 C Y Z
        (@computational_pushout_object C P t S X Y Z alpha gamma Q)
        (@computational_pushout_inj2 C P t S X Y Z alpha gamma Q) gamma))
≔ @abelian_group_sub_zero_to_eq_path
    (Hom C Y
      (@computational_pushout_object C P t S X Y Z alpha gamma Q))
    (@preadditive_hom_structure C
      (@additive_preadditive C P t S) Y
      (@computational_pushout_object C P t S X Y Z alpha gamma Q))
    (@comp_fapp0 C Y X
      (@computational_pushout_object C P t S X Y Z alpha gamma Q)
      (@computational_pushout_inj1 C P t S X Y Z alpha gamma Q) alpha)
    (@comp_fapp0 C Y Z
      (@computational_pushout_object C P t S X Y Z alpha gamma Q)
      (@computational_pushout_inj2 C P t S X Y Z alpha gamma Q) gamma)
    (@eq_trans _ _ _ _
      (@eq_sym _ _ _
        (@computational_pushout_difference_expansion_path C P t S
          X Y Z alpha gamma Q))
      (@computational_cokernel_annihilation C
        (@additive_preadditive C P t S)
        Y (@pushout_product_object C P t S X Z)
        (@pushout_difference_fapp0 C P t S X Y Z alpha gamma) Q));

// Primary cocones are coannihilator fibres of the difference map.
symbol PushoutCocone
  [C : Cat]
  [P : τ (Functor (Product_cat C C) C)]
  [t : τ (Obj C)]
  (S : τ (@AdditiveCategory C P t))
  [X Y Z : τ (Obj C)]
  (alpha : τ (Hom C Y X))
  (gamma : τ (Hom C Y Z))
  (T : τ (Obj C))
  : Grpd
≔ @CokernelCoannihilator C
    (@additive_preadditive C P t S)
    Y (@pushout_product_object C P t S X Z)
    (@pushout_difference_fapp0 C P t S X Y Z alpha gamma) T;

symbol pushout_cocone_morphism
  [C : Cat]
  [P : τ (Functor (Product_cat C C) C)]
  [t : τ (Obj C)]
  [S : τ (@AdditiveCategory C P t)]
  [X Y Z T : τ (Obj C)]
  [alpha : τ (Hom C Y X)]
  [gamma : τ (Hom C Y Z)]
  (cone : τ (@PushoutCocone C P t S X Y Z alpha gamma T))
  : τ (Hom C (@pushout_product_object C P t S X Z) T)
≔ @cokernel_coannihilator_arrow C
    (@additive_preadditive C P t S)
    Y (@pushout_product_object C P t S X Z)
    (@pushout_difference_fapp0 C P t S X Y Z alpha gamma) T cone;

symbol pushout_cocone_inj1
  [C : Cat]
  [P : τ (Functor (Product_cat C C) C)]
  [t : τ (Obj C)]
  [S : τ (@AdditiveCategory C P t)]
  [X Y Z T : τ (Obj C)]
  [alpha : τ (Hom C Y X)]
  [gamma : τ (Hom C Y Z)]
  (cone : τ (@PushoutCocone C P t S X Y Z alpha gamma T))
  : τ (Hom C X T)
≔ @comp_fapp0 C X
    (@pushout_product_object C P t S X Z) T
    (@pushout_cocone_morphism C P t S X Y Z T alpha gamma cone)
    (@additive_inj1_fapp0 C P t S X Z);

symbol pushout_cocone_inj2
  [C : Cat]
  [P : τ (Functor (Product_cat C C) C)]
  [t : τ (Obj C)]
  [S : τ (@AdditiveCategory C P t)]
  [X Y Z T : τ (Obj C)]
  [alpha : τ (Hom C Y X)]
  [gamma : τ (Hom C Y Z)]
  (cone : τ (@PushoutCocone C P t S X Y Z alpha gamma T))
  : τ (Hom C Z T)
≔ @comp_fapp0 C Z
    (@pushout_product_object C P t S X Z) T
    (@pushout_cocone_morphism C P t S X Y Z T alpha gamma cone)
    (@additive_inj2_fapp0 C P t S X Z);

symbol pushout_copair_fapp0
  [C : Cat]
  [P : τ (Functor (Product_cat C C) C)]
  [t : τ (Obj C)]
  [S : τ (@AdditiveCategory C P t)]
  [X Z T : τ (Obj C)]
  (a : τ (Hom C X T))
  (b : τ (Hom C Z T))
  : τ (Hom C (@pushout_product_object C P t S X Z) T)
≔ @additive_copair_fapp0 C P t S X Z T a b;

// Copairing expands the span difference to a o alpha - b o gamma.
symbol pushout_difference_copair_path
  [C : Cat]
  [P : τ (Functor (Product_cat C C) C)]
  [t : τ (Obj C)]
  [S : τ (@AdditiveCategory C P t)]
  [X Y Z T : τ (Obj C)]
  (alpha : τ (Hom C Y X))
  (gamma : τ (Hom C Y Z))
  (a : τ (Hom C X T))
  (b : τ (Hom C Z T))
  : τ (@= (Hom C Y T)
      (@comp_fapp0 C Y
        (@pushout_product_object C P t S X Z) T
        (@pushout_copair_fapp0 C P t S X Z T a b)
        (@pushout_difference_fapp0 C P t S X Y Z alpha gamma))
      (@preadditive_hom_add C
        (@additive_preadditive C P t S) Y T
        (@comp_fapp0 C Y X T a alpha)
        (@preadditive_hom_neg C
          (@additive_preadditive C P t S) Y T
          (@comp_fapp0 C Y Z T b gamma))))
≔ @eq_trans (Hom C Y T)
    (@comp_fapp0 C Y
      (@pushout_product_object C P t S X Z) T
      (@pushout_copair_fapp0 C P t S X Z T a b)
      (@pushout_difference_fapp0 C P t S X Y Z alpha gamma))
    (@preadditive_hom_add C
      (@additive_preadditive C P t S) Y T
      (@comp_fapp0 C Y
        (@pushout_product_object C P t S X Z) T
        (@pushout_copair_fapp0 C P t S X Z T a b)
        (@comp_fapp0 C Y X
          (@pushout_product_object C P t S X Z)
          (@additive_inj1_fapp0 C P t S X Z) alpha))
      (@comp_fapp0 C Y
        (@pushout_product_object C P t S X Z) T
        (@pushout_copair_fapp0 C P t S X Z T a b)
        (@comp_fapp0 C Y Z
          (@pushout_product_object C P t S X Z)
          (@additive_inj2_fapp0 C P t S X Z)
          (@preadditive_hom_neg C
            (@additive_preadditive C P t S) Y Z gamma))))
    (@preadditive_hom_add C
      (@additive_preadditive C P t S) Y T
      (@comp_fapp0 C Y X T a alpha)
      (@preadditive_hom_neg C
        (@additive_preadditive C P t S) Y T
        (@comp_fapp0 C Y Z T b gamma)))
    ((@preadditive_comp_add_right_law C
      (@additive_preadditive C P t S))
      Y (@pushout_product_object C P t S X Z) T
      (@pushout_copair_fapp0 C P t S X Z T a b)
      (@comp_fapp0 C Y X
        (@pushout_product_object C P t S X Z)
        (@additive_inj1_fapp0 C P t S X Z) alpha)
      (@comp_fapp0 C Y Z
        (@pushout_product_object C P t S X Z)
        (@additive_inj2_fapp0 C P t S X Z)
        (@preadditive_hom_neg C
          (@additive_preadditive C P t S) Y Z gamma)))
    (@additive_add_congr_path C P t S Y T _ _ _ _
      (@eq_trans (Hom C Y T)
        (@comp_fapp0 C Y
          (@pushout_product_object C P t S X Z) T
          (@pushout_copair_fapp0 C P t S X Z T a b)
          (@comp_fapp0 C Y X
            (@pushout_product_object C P t S X Z)
            (@additive_inj1_fapp0 C P t S X Z) alpha))
        (@comp_fapp0 C Y X T
          (@comp_fapp0 C X
            (@pushout_product_object C P t S X Z) T
            (@pushout_copair_fapp0 C P t S X Z T a b)
            (@additive_inj1_fapp0 C P t S X Z))
          alpha)
        (@comp_fapp0 C Y X T a alpha)
        (@comp_assoc C Y X
          (@pushout_product_object C P t S X Z) T
          (@pushout_copair_fapp0 C P t S X Z T a b)
          (@additive_inj1_fapp0 C P t S X Z) alpha)
        (@eq_ap (Hom C X T) (Hom C Y T)
          (λ h : τ (Hom C X T), @comp_fapp0 C Y X T h alpha)
          _ a
          (@additive_copair_inj1_path C P t S X Z T a b)))
      (@eq_trans (Hom C Y T)
        (@comp_fapp0 C Y
          (@pushout_product_object C P t S X Z) T
          (@pushout_copair_fapp0 C P t S X Z T a b)
          (@comp_fapp0 C Y Z
            (@pushout_product_object C P t S X Z)
            (@additive_inj2_fapp0 C P t S X Z)
            (@preadditive_hom_neg C
              (@additive_preadditive C P t S) Y Z gamma)))
        (@comp_fapp0 C Y Z T
          (@comp_fapp0 C Z
            (@pushout_product_object C P t S X Z) T
            (@pushout_copair_fapp0 C P t S X Z T a b)
            (@additive_inj2_fapp0 C P t S X Z))
          (@preadditive_hom_neg C
            (@additive_preadditive C P t S) Y Z gamma))
        (@preadditive_hom_neg C
          (@additive_preadditive C P t S) Y T
          (@comp_fapp0 C Y Z T b gamma))
        (@comp_assoc C Y Z
          (@pushout_product_object C P t S X Z) T
          (@pushout_copair_fapp0 C P t S X Z T a b)
          (@additive_inj2_fapp0 C P t S X Z)
          (@preadditive_hom_neg C
            (@additive_preadditive C P t S) Y Z gamma))
        (@eq_trans (Hom C Y T)
          (@comp_fapp0 C Y Z T
            (@comp_fapp0 C Z
              (@pushout_product_object C P t S X Z) T
              (@pushout_copair_fapp0 C P t S X Z T a b)
              (@additive_inj2_fapp0 C P t S X Z))
            (@preadditive_hom_neg C
              (@additive_preadditive C P t S) Y Z gamma))
          (@comp_fapp0 C Y Z T b
            (@preadditive_hom_neg C
              (@additive_preadditive C P t S) Y Z gamma))
          (@preadditive_hom_neg C
            (@additive_preadditive C P t S) Y T
            (@comp_fapp0 C Y Z T b gamma))
          (@eq_ap (Hom C Z T) (Hom C Y T)
            (λ h : τ (Hom C Z T),
              @comp_fapp0 C Y Z T h
                (@preadditive_hom_neg C
                  (@additive_preadditive C P t S) Y Z gamma))
            _ b
            (@additive_copair_inj2_path C P t S X Z T a b))
          (@preadditive_comp_neg_right_path C
            (@additive_preadditive C P t S) Y Z T b gamma))));

// A conventional compatible copair becomes the primary coannihilator cone.
symbol pushout_cocone_intro
  [C : Cat]
  [P : τ (Functor (Product_cat C C) C)]
  [t : τ (Obj C)]
  [S : τ (@AdditiveCategory C P t)]
  [X Y Z T : τ (Obj C)]
  (alpha : τ (Hom C Y X))
  (gamma : τ (Hom C Y Z))
  (a : τ (Hom C X T))
  (b : τ (Hom C Z T))
  (compatibility : τ (@= (Hom C Y T)
    (@comp_fapp0 C Y X T a alpha)
    (@comp_fapp0 C Y Z T b gamma)))
  : τ (@PushoutCocone C P t S X Y Z alpha gamma T)
≔ @Struct_sigma
    (Hom C (@pushout_product_object C P t S X Z) T)
    (λ u : τ (Hom C (@pushout_product_object C P t S X Z) T),
      @= (Hom C Y T)
        (@comp_fapp0 C Y
          (@pushout_product_object C P t S X Z) T u
          (@pushout_difference_fapp0 C P t S X Y Z alpha gamma))
        (@preadditive_hom_zero C
          (@additive_preadditive C P t S) Y T))
    (@pushout_copair_fapp0 C P t S X Z T a b)
    (@eq_trans (Hom C Y T) _ _ _
      (@pushout_difference_copair_path C P t S X Y Z T
        alpha gamma a b)
      (@eq_trans (Hom C Y T) _ _ _
        (@additive_add_congr_path C P t S Y T _ _ _ _
          compatibility
          (@eq_refl (Hom C Y T)
            (@preadditive_hom_neg C
              (@additive_preadditive C P t S) Y T
              (@comp_fapp0 C Y Z T b gamma))))
        ((@abelian_group_add_inv_law
          (Hom C Y T)
          (@preadditive_hom_structure C
            (@additive_preadditive C P t S) Y T))
          (@comp_fapp0 C Y Z T b gamma))));

symbol PushoutCofactorSpace
  [C : Cat]
  [P : τ (Functor (Product_cat C C) C)]
  [t : τ (Obj C)]
  [S : τ (@AdditiveCategory C P t)]
  [X Y Z : τ (Obj C)]
  [alpha : τ (Hom C Y X)]
  [gamma : τ (Hom C Y Z)]
  (Q : τ (@ComputationalPushout C P t S X Y Z alpha gamma))
  (T : τ (Obj C))
  (cone : τ (@PushoutCocone C P t S X Y Z alpha gamma T))
  : Grpd
≔ @CokernelFactorSpace C
    (@additive_preadditive C P t S)
    Y (@pushout_product_object C P t S X Z)
    (@pushout_difference_fapp0 C P t S X Y Z alpha gamma)
    (@computational_pushout_object C P t S X Y Z alpha gamma Q)
    (@computational_pushout_morphism C P t S X Y Z alpha gamma Q)
    T cone;

symbol computational_pushout_cofactor_contr
  [C : Cat]
  [P : τ (Functor (Product_cat C C) C)]
  [t : τ (Obj C)]
  [S : τ (@AdditiveCategory C P t)]
  [X Y Z : τ (Obj C)]
  [alpha : τ (Hom C Y X)]
  [gamma : τ (Hom C Y Z)]
  (Q : τ (@ComputationalPushout C P t S X Y Z alpha gamma))
  (T : τ (Obj C))
  (cone : τ (@PushoutCocone C P t S X Y Z alpha gamma T))
  : τ (IsContr (@PushoutCofactorSpace C P t S X Y Z
      alpha gamma Q T cone))
≔ @computational_cokernel_factor_contr C
    (@additive_preadditive C P t S)
    Y (@pushout_product_object C P t S X Z)
    (@pushout_difference_fapp0 C P t S X Y Z alpha gamma)
    Q T cone;

symbol computational_pushout_cofactor
  [C : Cat]
  [P : τ (Functor (Product_cat C C) C)]
  [t : τ (Obj C)]
  [S : τ (@AdditiveCategory C P t)]
  [X Y Z : τ (Obj C)]
  [alpha : τ (Hom C Y X)]
  [gamma : τ (Hom C Y Z)]
  (Q : τ (@ComputationalPushout C P t S X Y Z alpha gamma))
  (T : τ (Obj C))
  (cone : τ (@PushoutCocone C P t S X Y Z alpha gamma T))
  : τ (Hom C
      (@computational_pushout_object C P t S X Y Z alpha gamma Q) T)
≔ @computational_cokernel_colift C
    (@additive_preadditive C P t S)
    Y (@pushout_product_object C P t S X Z)
    (@pushout_difference_fapp0 C P t S X Y Z alpha gamma)
    Q T cone;

symbol computational_pushout_cofactor_path
  [C : Cat]
  [P : τ (Functor (Product_cat C C) C)]
  [t : τ (Obj C)]
  [S : τ (@AdditiveCategory C P t)]
  [X Y Z : τ (Obj C)]
  [alpha : τ (Hom C Y X)]
  [gamma : τ (Hom C Y Z)]
  (Q : τ (@ComputationalPushout C P t S X Y Z alpha gamma))
  (T : τ (Obj C))
  (cone : τ (@PushoutCocone C P t S X Y Z alpha gamma T))
  : τ (@= (Hom C (@pushout_product_object C P t S X Z) T)
      (@comp_fapp0 C
        (@pushout_product_object C P t S X Z)
        (@computational_pushout_object C P t S X Y Z alpha gamma Q) T
        (@computational_pushout_cofactor C P t S X Y Z alpha gamma Q T cone)
        (@computational_pushout_morphism C P t S X Y Z alpha gamma Q))
      (@cokernel_coannihilator_arrow C
        (@additive_preadditive C P t S)
        Y (@pushout_product_object C P t S X Z)
        (@pushout_difference_fapp0 C P t S X Y Z alpha gamma) T cone))
≔ @computational_cokernel_colift_path C
    (@additive_preadditive C P t S)
    Y (@pushout_product_object C P t S X Z)
    (@pushout_difference_fapp0 C P t S X Y Z alpha gamma)
    Q T cone;

symbol computational_pushout_cofactor_inj1_path
  [C : Cat]
  [P : τ (Functor (Product_cat C C) C)]
  [t : τ (Obj C)]
  [S : τ (@AdditiveCategory C P t)]
  [X Y Z : τ (Obj C)]
  [alpha : τ (Hom C Y X)]
  [gamma : τ (Hom C Y Z)]
  (Q : τ (@ComputationalPushout C P t S X Y Z alpha gamma))
  (T : τ (Obj C))
  (cone : τ (@PushoutCocone C P t S X Y Z alpha gamma T))
  : τ (@= (Hom C X T)
      (@comp_fapp0 C X
        (@computational_pushout_object C P t S X Y Z alpha gamma Q) T
        (@computational_pushout_cofactor C P t S X Y Z alpha gamma Q T cone)
        (@computational_pushout_inj1 C P t S X Y Z alpha gamma Q))
      (@pushout_cocone_inj1 C P t S X Y Z T alpha gamma cone))
≔ @eq_trans (Hom C X T) _ _ _
    (@comp_assoc C X
      (@pushout_product_object C P t S X Z)
      (@computational_pushout_object C P t S X Y Z alpha gamma Q) T
      (@computational_pushout_cofactor C P t S X Y Z alpha gamma Q T cone)
      (@computational_pushout_morphism C P t S X Y Z alpha gamma Q)
      (@additive_inj1_fapp0 C P t S X Z))
    (@eq_ap
      (Hom C (@pushout_product_object C P t S X Z) T)
      (Hom C X T)
      (λ h : τ (Hom C (@pushout_product_object C P t S X Z) T),
        @comp_fapp0 C X (@pushout_product_object C P t S X Z) T h
          (@additive_inj1_fapp0 C P t S X Z))
      _ _
      (@computational_pushout_cofactor_path C P t S
        X Y Z alpha gamma Q T cone));

symbol computational_pushout_cofactor_inj2_path
  [C : Cat]
  [P : τ (Functor (Product_cat C C) C)]
  [t : τ (Obj C)]
  [S : τ (@AdditiveCategory C P t)]
  [X Y Z : τ (Obj C)]
  [alpha : τ (Hom C Y X)]
  [gamma : τ (Hom C Y Z)]
  (Q : τ (@ComputationalPushout C P t S X Y Z alpha gamma))
  (T : τ (Obj C))
  (cone : τ (@PushoutCocone C P t S X Y Z alpha gamma T))
  : τ (@= (Hom C Z T)
      (@comp_fapp0 C Z
        (@computational_pushout_object C P t S X Y Z alpha gamma Q) T
        (@computational_pushout_cofactor C P t S X Y Z alpha gamma Q T cone)
        (@computational_pushout_inj2 C P t S X Y Z alpha gamma Q))
      (@pushout_cocone_inj2 C P t S X Y Z T alpha gamma cone))
≔ @eq_trans (Hom C Z T) _ _ _
    (@comp_assoc C Z
      (@pushout_product_object C P t S X Z)
      (@computational_pushout_object C P t S X Y Z alpha gamma Q) T
      (@computational_pushout_cofactor C P t S X Y Z alpha gamma Q T cone)
      (@computational_pushout_morphism C P t S X Y Z alpha gamma Q)
      (@additive_inj2_fapp0 C P t S X Z))
    (@eq_ap
      (Hom C (@pushout_product_object C P t S X Z) T)
      (Hom C Z T)
      (λ h : τ (Hom C (@pushout_product_object C P t S X Z) T),
        @comp_fapp0 C Z (@pushout_product_object C P t S X Z) T h
          (@additive_inj2_fapp0 C P t S X Z))
      _ _
      (@computational_pushout_cofactor_path C P t S
        X Y Z alpha gamma Q T cone));

symbol computational_pushout_cofactor_unique_path
  [C : Cat]
  [P : τ (Functor (Product_cat C C) C)]
  [t : τ (Obj C)]
  [S : τ (@AdditiveCategory C P t)]
  [X Y Z : τ (Obj C)]
  [alpha : τ (Hom C Y X)]
  [gamma : τ (Hom C Y Z)]
  (Q : τ (@ComputationalPushout C P t S X Y Z alpha gamma))
  (T : τ (Obj C))
  (cone : τ (@PushoutCocone C P t S X Y Z alpha gamma T))
  (u : τ (Hom C
    (@computational_pushout_object C P t S X Y Z alpha gamma Q) T))
  (p : τ (@= (Hom C (@pushout_product_object C P t S X Z) T)
    (@comp_fapp0 C
      (@pushout_product_object C P t S X Z)
      (@computational_pushout_object C P t S X Y Z alpha gamma Q) T
      u (@computational_pushout_morphism C P t S X Y Z alpha gamma Q))
    (@cokernel_coannihilator_arrow C
      (@additive_preadditive C P t S)
      Y (@pushout_product_object C P t S X Z)
      (@pushout_difference_fapp0 C P t S X Y Z alpha gamma) T cone)))
  : τ (@= (Hom C
      (@computational_pushout_object C P t S X Y Z alpha gamma Q) T)
      (@computational_pushout_cofactor C P t S X Y Z alpha gamma Q T cone)
      u)
≔ @computational_cokernel_colift_unique_path C
    (@additive_preadditive C P t S)
    Y (@pushout_product_object C P t S X Z)
    (@pushout_difference_fapp0 C P t S X Y Z alpha gamma)
    Q T cone u p;

symbol HasComputationalPushouts
  [C : Cat]
  [P : τ (Functor (Product_cat C C) C)]
  [t : τ (Obj C)]
  (S : τ (@AdditiveCategory C P t))
  : Grpd
≔ @Pi_grpd (Obj C) (λ X : τ (Obj C),
    @Pi_grpd (Obj C) (λ Y : τ (Obj C),
      @Pi_grpd (Obj C) (λ Z : τ (Obj C),
        @Pi_grpd (Hom C Y X) (λ alpha : τ (Hom C Y X),
          @Pi_grpd (Hom C Y Z) (λ gamma : τ (Hom C Y Z),
            @ComputationalPushout C P t S X Y Z alpha gamma)))));

symbol computational_cokernels_give_pushouts
  [C : Cat]
  [P : τ (Functor (Product_cat C C) C)]
  [t : τ (Obj C)]
  (S : τ (@AdditiveCategory C P t))
  (Q : τ (@HasComputationalCokernels C
    (@additive_preadditive C P t S)))
  : τ (@HasComputationalPushouts C P t S)
≔ λ X : τ (Obj C), λ Y : τ (Obj C), λ Z : τ (Obj C),
    λ alpha : τ (Hom C Y X), λ gamma : τ (Hom C Y Z),
      @computational_pushout_of_cokernels C P t S Q
        X Y Z alpha gamma;
