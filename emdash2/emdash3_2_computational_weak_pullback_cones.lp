/*
  Explicit equalizing pairs become internal difference-encoded cones.

  Pairing is the existing whole product operation. Bilinearity, triangular
  beta, preservation of negation, and the supplied compatibility path prove
  that `[alpha,-gamma] o <a,b> = 0`. No square record is introduced.
*/

require open emdash.emdash3_2_computational_weak_pullback_compatibility;

symbol weak_pullback_pair_fapp0
  [C : Cat]
  [P : τ (Functor (Product_cat C C) C)]
  [t : τ (Obj C)]
  [S : τ (@AdditiveCategory C P t)]
  [X Z T : τ (Obj C)]
  (a : τ (Hom C T X))
  (b : τ (Hom C T Z))
  : τ (Hom C T (@weak_pullback_product_object C P t S X Z))
≔ @binary_products_pair_fapp0 C P
    (@additive_binary_products C P t S) T X Z a b;

symbol weak_pullback_difference_pair_path
  [C : Cat]
  [P : τ (Functor (Product_cat C C) C)]
  [t : τ (Obj C)]
  [S : τ (@AdditiveCategory C P t)]
  [X Y Z T : τ (Obj C)]
  (alpha : τ (Hom C X Y))
  (gamma : τ (Hom C Z Y))
  (a : τ (Hom C T X))
  (b : τ (Hom C T Z))
  : τ (@= (Hom C T Y)
      (@comp_fapp0 C T
        (@weak_pullback_product_object C P t S X Z) Y
        (@weak_pullback_difference_fapp0 C P t S X Y Z alpha gamma)
        (@weak_pullback_pair_fapp0 C P t S X Z T a b))
      (@preadditive_hom_add C
        (@additive_preadditive C P t S) T Y
        (@comp_fapp0 C T X Y alpha a)
        (@preadditive_hom_neg C
          (@additive_preadditive C P t S) T Y
          (@comp_fapp0 C T Z Y gamma b))))
≔ @eq_trans _ _
    (@preadditive_hom_add C
      (@additive_preadditive C P t S) T Y
      (@comp_fapp0 C T
        (@weak_pullback_product_object C P t S X Z) Y
        (@comp_fapp0 C
          (@weak_pullback_product_object C P t S X Z) X Y alpha
          (@binary_products_proj1_fapp0 C P
            (@additive_binary_products C P t S) X Z))
        (@weak_pullback_pair_fapp0 C P t S X Z T a b))
      (@comp_fapp0 C T
        (@weak_pullback_product_object C P t S X Z) Y
        (@comp_fapp0 C
          (@weak_pullback_product_object C P t S X Z) Z Y
          (@preadditive_hom_neg C
            (@additive_preadditive C P t S) Z Y gamma)
          (@binary_products_proj2_fapp0 C P
            (@additive_binary_products C P t S) X Z))
        (@weak_pullback_pair_fapp0 C P t S X Z T a b)))
    _
    ((@preadditive_comp_add_left_law C
      (@additive_preadditive C P t S))
      T (@weak_pullback_product_object C P t S X Z) Y
      (@comp_fapp0 C
        (@weak_pullback_product_object C P t S X Z) X Y alpha
        (@binary_products_proj1_fapp0 C P
          (@additive_binary_products C P t S) X Z))
      (@comp_fapp0 C
        (@weak_pullback_product_object C P t S X Z) Z Y
        (@preadditive_hom_neg C
          (@additive_preadditive C P t S) Z Y gamma)
        (@binary_products_proj2_fapp0 C P
          (@additive_binary_products C P t S) X Z))
      (@weak_pullback_pair_fapp0 C P t S X Z T a b))
    (@additive_add_congr_path C P t S T Y _ _ _ _
      (@eq_sym _ _ _
        (@comp_assoc C T
          (@weak_pullback_product_object C P t S X Z) X Y
          alpha
          (@binary_products_proj1_fapp0 C P
            (@additive_binary_products C P t S) X Z)
          (@weak_pullback_pair_fapp0 C P t S X Z T a b)))
      (@eq_trans _ _
        (@comp_fapp0 C T Z Y
          (@preadditive_hom_neg C
            (@additive_preadditive C P t S) Z Y gamma) b)
        _
        (@eq_sym _ _ _
          (@comp_assoc C T
            (@weak_pullback_product_object C P t S X Z) Z Y
            (@preadditive_hom_neg C
              (@additive_preadditive C P t S) Z Y gamma)
            (@binary_products_proj2_fapp0 C P
              (@additive_binary_products C P t S) X Z)
            (@weak_pullback_pair_fapp0 C P t S X Z T a b)))
        (@preadditive_comp_neg_left_path C
          (@additive_preadditive C P t S) T Z Y gamma b)));

symbol weak_pullback_cone_intro
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
  : τ (@WeakPullbackCone C P t S X Y Z alpha gamma T)
≔ @Struct_sigma
    (Hom C T (@weak_pullback_product_object C P t S X Z))
    (λ u : τ (Hom C T (@weak_pullback_product_object C P t S X Z)),
      @= (Hom C T Y)
        (@comp_fapp0 C T
          (@weak_pullback_product_object C P t S X Z) Y
          (@weak_pullback_difference_fapp0 C P t S X Y Z alpha gamma) u)
        (@preadditive_hom_zero C
          (@additive_preadditive C P t S) T Y))
    (@weak_pullback_pair_fapp0 C P t S X Z T a b)
    (@eq_trans (Hom C T Y) _ _ _
      (@weak_pullback_difference_pair_path
        C P t S X Y Z T alpha gamma a b)
      (@eq_trans (Hom C T Y) _ _ _
        (@additive_add_congr_path C P t S T Y _ _ _ _
          compatibility
          (@eq_refl (Hom C T Y)
            (@preadditive_hom_neg C
              (@additive_preadditive C P t S) T Y
              (@comp_fapp0 C T Z Y gamma b))))
        ((@abelian_group_add_inv_law
          (Hom C T Y)
          (@preadditive_hom_structure C
            (@additive_preadditive C P t S) T Y))
          (@comp_fapp0 C T Z Y gamma b))));
