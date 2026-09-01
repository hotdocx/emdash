/*
  Ordinary compatibility of difference-encoded computational weak pullbacks.

  Generic abelian-group cancellation and preservation of negation by
  precomposition expand `[alpha,-gamma] o kappa = 0` into
  `alpha o p = gamma o q`. This theorem layer adds no alternate cone carrier
  and no rewrite/unification rule.
*/

require open emdash.emdash3_2_computational_weak_pullbacks;

symbol abelian_group_add_inverse_unique_path
  [A : Grpd]
  (S : τ (@AbelianGroupStructure A))
  (a b : τ A)
  (law : τ (@= A
    (@abelian_group_ops_add A
      (@abelian_group_structure_ops A S) a b)
    (@abelian_group_ops_zero A
      (@abelian_group_structure_ops A S))))
  : τ (@= A b
      (@abelian_group_ops_neg A
        (@abelian_group_structure_ops A S) a))
≔ @eq_trans A
    b
    (@abelian_group_ops_add A
      (@abelian_group_structure_ops A S)
      (@abelian_group_ops_zero A
        (@abelian_group_structure_ops A S)) b)
    (@abelian_group_ops_neg A
      (@abelian_group_structure_ops A S) a)
    (@eq_sym A _ b (@abelian_group_add_zero_left_path A S b))
    (@eq_trans A _
      (@abelian_group_ops_add A
        (@abelian_group_structure_ops A S)
        (@abelian_group_ops_add A
          (@abelian_group_structure_ops A S)
          (@abelian_group_ops_neg A
            (@abelian_group_structure_ops A S) a) a)
        b)
      (@abelian_group_ops_neg A
        (@abelian_group_structure_ops A S) a)
      (@eq_ap A A
        (λ z : τ A,
          @abelian_group_ops_add A
            (@abelian_group_structure_ops A S) z b)
        (@abelian_group_ops_zero A
          (@abelian_group_structure_ops A S))
        (@abelian_group_ops_add A
          (@abelian_group_structure_ops A S)
          (@abelian_group_ops_neg A
            (@abelian_group_structure_ops A S) a) a)
        (@eq_sym A _ _ (@abelian_group_add_inv_left_path A S a)))
      (@eq_trans A _
        (@abelian_group_ops_add A
          (@abelian_group_structure_ops A S)
          (@abelian_group_ops_neg A
            (@abelian_group_structure_ops A S) a)
          (@abelian_group_ops_add A
            (@abelian_group_structure_ops A S) a b))
        (@abelian_group_ops_neg A
          (@abelian_group_structure_ops A S) a)
        (@abelian_group_add_assoc_law A S
          (@abelian_group_ops_neg A
            (@abelian_group_structure_ops A S) a) a b)
        (@eq_trans A _
          (@abelian_group_ops_add A
            (@abelian_group_structure_ops A S)
            (@abelian_group_ops_neg A
              (@abelian_group_structure_ops A S) a)
            (@abelian_group_ops_zero A
              (@abelian_group_structure_ops A S)))
          (@abelian_group_ops_neg A
            (@abelian_group_structure_ops A S) a)
          (@eq_ap A A
            (λ z : τ A,
              @abelian_group_ops_add A
                (@abelian_group_structure_ops A S)
                (@abelian_group_ops_neg A
                  (@abelian_group_structure_ops A S) a) z)
            (@abelian_group_ops_add A
              (@abelian_group_structure_ops A S) a b)
            (@abelian_group_ops_zero A
              (@abelian_group_structure_ops A S))
            law)
          (@abelian_group_add_zero_law A S
            (@abelian_group_ops_neg A
              (@abelian_group_structure_ops A S) a)))));

symbol abelian_group_neg_involutive_path
  [A : Grpd]
  (S : τ (@AbelianGroupStructure A))
  (a : τ A)
  : τ (@= A
      (@abelian_group_ops_neg A
        (@abelian_group_structure_ops A S)
        (@abelian_group_ops_neg A
          (@abelian_group_structure_ops A S) a))
      a)
≔ @eq_sym A a _
    (@abelian_group_add_inverse_unique_path A S
      (@abelian_group_ops_neg A
        (@abelian_group_structure_ops A S) a)
      a
      (@abelian_group_add_inv_left_path A S a));

symbol abelian_group_sub_zero_to_eq_path
  [A : Grpd]
  (S : τ (@AbelianGroupStructure A))
  (a b : τ A)
  (law : τ (@= A
    (@abelian_group_ops_add A
      (@abelian_group_structure_ops A S) a
      (@abelian_group_ops_neg A
        (@abelian_group_structure_ops A S) b))
    (@abelian_group_ops_zero A
      (@abelian_group_structure_ops A S))))
  : τ (@= A a b)
≔ @eq_trans A a
    (@abelian_group_ops_neg A
      (@abelian_group_structure_ops A S)
      (@abelian_group_ops_neg A
        (@abelian_group_structure_ops A S) a))
    b
    (@eq_sym A _ a (@abelian_group_neg_involutive_path A S a))
    (@eq_trans A _
      (@abelian_group_ops_neg A
        (@abelian_group_structure_ops A S)
        (@abelian_group_ops_neg A
          (@abelian_group_structure_ops A S) b))
      b
      (@eq_ap A A
        (λ z : τ A,
          @abelian_group_ops_neg A
            (@abelian_group_structure_ops A S) z)
        (@abelian_group_ops_neg A
          (@abelian_group_structure_ops A S) a)
        (@abelian_group_ops_neg A
          (@abelian_group_structure_ops A S) b)
        (@eq_sym A _ _
          (@abelian_group_add_inverse_unique_path A S a
            (@abelian_group_ops_neg A
              (@abelian_group_structure_ops A S) b)
            law)))
      (@abelian_group_neg_involutive_path A S b));

// Precomposition preserves additive inverse in the left/output argument.
symbol preadditive_comp_neg_left_path
  [C : Cat]
  (S : τ (@PreadditiveCategory C))
  [X Y Z : τ (Obj C)]
  (g : τ (Hom C Y Z))
  (f : τ (Hom C X Y))
  : τ (@= (Hom C X Z)
      (@comp_fapp0 C X Y Z
        (@preadditive_hom_neg C S Y Z g) f)
      (@preadditive_hom_neg C S X Z
        (@comp_fapp0 C X Y Z g f)))
≔ @abelian_group_add_inverse_unique_path
    (Hom C X Z)
    (@preadditive_hom_structure C S X Z)
    (@comp_fapp0 C X Y Z g f)
    (@comp_fapp0 C X Y Z
      (@preadditive_hom_neg C S Y Z g) f)
    (@eq_trans (Hom C X Z) _ _ _
      (@eq_sym (Hom C X Z) _ _
        ((@preadditive_comp_add_left_law C S)
          X Y Z g (@preadditive_hom_neg C S Y Z g) f))
      (@eq_trans (Hom C X Z) _ _ _
        (@eq_ap (Hom C Y Z) (Hom C X Z)
          (λ q : τ (Hom C Y Z), @comp_fapp0 C X Y Z q f)
          (@preadditive_hom_add C S Y Z g
            (@preadditive_hom_neg C S Y Z g))
          (@preadditive_hom_zero C S Y Z)
          ((@abelian_group_add_inv_law
            (Hom C Y Z)
            (@preadditive_hom_structure C S Y Z)) g))
        (@preadditive_comp_zero_left_path C S X Y Z f)));

// Expand [alpha,-gamma] o kappa into alpha o p + -(gamma o q).
symbol computational_weak_pullback_difference_expansion_path
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
      (@preadditive_hom_add C
        (@additive_preadditive C P t S)
        (@computational_weak_pullback_object C P t S X Y Z alpha gamma W) Y
        (@comp_fapp0 C
          (@computational_weak_pullback_object C P t S X Y Z alpha gamma W)
          X Y alpha
          (@computational_weak_pullback_proj1 C P t S X Y Z alpha gamma W))
        (@preadditive_hom_neg C
          (@additive_preadditive C P t S)
          (@computational_weak_pullback_object C P t S X Y Z alpha gamma W) Y
          (@comp_fapp0 C
            (@computational_weak_pullback_object C P t S X Y Z alpha gamma W)
            Z Y gamma
            (@computational_weak_pullback_proj2 C P t S X Y Z alpha gamma W)))))
≔ @eq_trans _ _
    (@preadditive_hom_add C
      (@additive_preadditive C P t S)
      (@computational_weak_pullback_object C P t S X Y Z alpha gamma W) Y
      (@comp_fapp0 C
        (@computational_weak_pullback_object C P t S X Y Z alpha gamma W)
        (@weak_pullback_product_object C P t S X Z) Y
        (@comp_fapp0 C
          (@weak_pullback_product_object C P t S X Z) X Y alpha
          (@binary_products_proj1_fapp0 C P
            (@additive_binary_products C P t S) X Z))
        (@computational_weak_pullback_morphism C P t S X Y Z alpha gamma W))
      (@comp_fapp0 C
        (@computational_weak_pullback_object C P t S X Y Z alpha gamma W)
        (@weak_pullback_product_object C P t S X Z) Y
        (@comp_fapp0 C
          (@weak_pullback_product_object C P t S X Z) Z Y
          (@preadditive_hom_neg C
            (@additive_preadditive C P t S) Z Y gamma)
          (@binary_products_proj2_fapp0 C P
            (@additive_binary_products C P t S) X Z))
        (@computational_weak_pullback_morphism C P t S X Y Z alpha gamma W)))
    _
    ((@preadditive_comp_add_left_law C
      (@additive_preadditive C P t S))
      (@computational_weak_pullback_object C P t S X Y Z alpha gamma W)
      (@weak_pullback_product_object C P t S X Z) Y
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
      (@computational_weak_pullback_morphism C P t S X Y Z alpha gamma W))
    (@additive_add_congr_path C P t S
      _ _ _ _ _ _
      (@eq_sym _ _ _
        (@comp_assoc C
          (@computational_weak_pullback_object C P t S X Y Z alpha gamma W)
          (@weak_pullback_product_object C P t S X Z) X Y
          alpha
          (@binary_products_proj1_fapp0 C P
            (@additive_binary_products C P t S) X Z)
          (@computational_weak_pullback_morphism C P t S X Y Z alpha gamma W)))
      (@eq_trans _ _
        (@comp_fapp0 C
          (@computational_weak_pullback_object C P t S X Y Z alpha gamma W)
          Z Y
          (@preadditive_hom_neg C
            (@additive_preadditive C P t S) Z Y gamma)
          (@computational_weak_pullback_proj2 C P t S X Y Z alpha gamma W))
        _
        (@eq_sym _ _ _
          (@comp_assoc C
            (@computational_weak_pullback_object C P t S X Y Z alpha gamma W)
            (@weak_pullback_product_object C P t S X Z) Z Y
            (@preadditive_hom_neg C
              (@additive_preadditive C P t S) Z Y gamma)
            (@binary_products_proj2_fapp0 C P
              (@additive_binary_products C P t S) X Z)
            (@computational_weak_pullback_morphism C P t S X Y Z alpha gamma W)))
        (@preadditive_comp_neg_left_path C
          (@additive_preadditive C P t S)
          (@computational_weak_pullback_object C P t S X Y Z alpha gamma W)
          Z Y gamma
          (@computational_weak_pullback_proj2 C P t S X Y Z alpha gamma W))));

symbol computational_weak_pullback_compatibility_path
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
        X Y alpha
        (@computational_weak_pullback_proj1 C P t S X Y Z alpha gamma W))
      (@comp_fapp0 C
        (@computational_weak_pullback_object C P t S X Y Z alpha gamma W)
        Z Y gamma
        (@computational_weak_pullback_proj2 C P t S X Y Z alpha gamma W)))
≔ @abelian_group_sub_zero_to_eq_path
    (Hom C
      (@computational_weak_pullback_object C P t S X Y Z alpha gamma W) Y)
    (@preadditive_hom_structure C
      (@additive_preadditive C P t S)
      (@computational_weak_pullback_object C P t S X Y Z alpha gamma W) Y)
    (@comp_fapp0 C
      (@computational_weak_pullback_object C P t S X Y Z alpha gamma W)
      X Y alpha
      (@computational_weak_pullback_proj1 C P t S X Y Z alpha gamma W))
    (@comp_fapp0 C
      (@computational_weak_pullback_object C P t S X Y Z alpha gamma W)
      Z Y gamma
      (@computational_weak_pullback_proj2 C P t S X Y Z alpha gamma W))
    (@eq_trans _ _ _ _
      (@eq_sym _ _ _
        (@computational_weak_pullback_difference_expansion_path
          C P t S X Y Z alpha gamma W))
      (@computational_weak_pullback_difference_path
        C P t S X Y Z alpha gamma W));
