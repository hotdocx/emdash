/* Whole addition from the two adjunctions at the same original Prod. */
require open emdash.emdash3_2_one_cat_copair_families;

// The addition functor uses both adjunctions at the same original Prod.
symbol one_cat_additive_family_add_func [B C : Cat] (C1 : τ (IsNCat (cat_succ cat_zero) C))
  [Prod : τ (Functor (Product_cat C C) C)] [t : τ (Obj C)]
  (A : τ (@AdditiveCategory C Prod t)) (T0 : τ (@TerminalObject (Op_cat C) t)) (X Y : τ (Functor B C))
  : τ (Functor (Product_cat (@Transf_cat B C X Y) (@Transf_cat B C X Y)) (@Transf_cat B C X Y))
≔ @comp_cat_fapp0 (Hom_cat (Functor_cat B (Product_cat C C)) (@Struct_sigma (Functor B C) (λ _ : τ (Functor B C),
  Functor B C) X X) (@fapp0 (Functor_cat B C) (Functor_cat B (Product_cat C C)) (@comp_cat_cov_func B C (Product_cat C
  C) (@product_diagonal_func C)) Y)) (@Transf_cat B C (@fapp0 (Functor_cat B (Product_cat C C)) (Functor_cat B C)
  (@comp_cat_cov_func B (Product_cat C C) C Prod) (@Struct_sigma (Functor B C) (λ _ : τ (Functor B C), Functor B C) X
  X)) Y) (@Transf_cat B C X Y)
    (@hom_precomp_along_func (Functor_cat B C) (Functor_cat B C) (@id_func (Functor_cat B C)) Y X (@fapp0 (Functor_cat
      B (Product_cat C C)) (Functor_cat B C) (@comp_cat_cov_func B (Product_cat C C) C Prod) (@Struct_sigma (Functor B
      C) (λ _ : τ (Functor B C), Functor B C) X X)) (@one_cat_product_family_pair B C C1 Prod
      (@additive_binary_products C Prod t A) X X X (@id (Functor_cat B C) X) (@id (Functor_cat B C) X)))
    (@one_cat_copair_family_func B C C1 Prod t A T0 X X Y);

// Add two whole transformations without supplying component naturality.
symbol one_cat_additive_family_add [B C : Cat] (C1 : τ (IsNCat (cat_succ cat_zero) C))
  [Prod : τ (Functor (Product_cat C C) C)] [t : τ (Obj C)]
  (A : τ (@AdditiveCategory C Prod t)) (T0 : τ (@TerminalObject (Op_cat C) t)) (X Y : τ (Functor B C))
  (f g : τ (@Transf B C X Y)) : τ (@Transf B C X Y)
≔ @fapp0 (Hom_cat (Functor_cat B (Product_cat C C)) (@Struct_sigma (Functor B C) (λ _ : τ (Functor B C), Functor B C)
  X X) (@fapp0 (Functor_cat B C) (Functor_cat B (Product_cat C C)) (@comp_cat_cov_func B C (Product_cat C C)
  (@product_diagonal_func C)) Y)) (@Transf_cat B C X Y) (@one_cat_additive_family_add_func B C C1 Prod t A T0 X
  Y) (@Struct_sigma (@Transf B C X Y) (λ _ : τ (@Transf B C X Y), @Transf B C X Y) f g);
