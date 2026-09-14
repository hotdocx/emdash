/* Original unit/counit observations of the explicit ordinary presentation. */
require open emdash.emdash3_2_one_cat_biproduct_adjunction;

assert [C : Cat] (C1 : τ (IsNCat (cat_succ cat_zero) C))
  [Prod : τ (Functor (Product_cat C C) C)] [t : τ (Obj C)]
  (A : τ (@AdditiveCategory C Prod t)) (T0 : τ (@TerminalObject (Op_cat C) t))
  ⊢ @unit_adj_transf (Product_cat C C) C Prod (@product_diagonal_func C)
      (@one_cat_biproduct_adjunction C C1 Prod t A T0)
    ≡ @Struct_sigma
        (@Transf (Product_cat C C) C (@Product_projL_func C C) Prod)
        (λ _ : τ (@Transf (Product_cat C C) C (@Product_projL_func C C) Prod),
          @Transf (Product_cat C C) C (@Product_projR_func C C) Prod)
        (@one_cat_biproduct_inj1 C C1 Prod t A T0)
        (@one_cat_biproduct_inj2 C C1 Prod t A T0);
assert [C : Cat] (C1 : τ (IsNCat (cat_succ cat_zero) C))
  [Prod : τ (Functor (Product_cat C C) C)] [t : τ (Obj C)]
  (A : τ (@AdditiveCategory C Prod t)) (T0 : τ (@TerminalObject (Op_cat C) t)) (X : τ (Obj C))
  ⊢ @tapp0_fapp0 C C (@comp_cat_fapp0 C (Product_cat C C) C Prod (@product_diagonal_func C)) (@id_func C) X
      (@counit_adj_transf (Product_cat C C) C Prod (@product_diagonal_func C)
        (@one_cat_biproduct_adjunction C C1 Prod t A T0))
    ≡ @additive_copair_fapp0 C Prod t A X X X (@id C X) (@id C X);

// A distinct supplied additive capability is not silently substituted.
assertnot [C : Cat] (C1 : τ (IsNCat (cat_succ cat_zero) C))
  [Prod : τ (Functor (Product_cat C C) C)] [t : τ (Obj C)]
  (A A1 : τ (@AdditiveCategory C Prod t)) (T0 : τ (@TerminalObject (Op_cat C) t))
  ⊢ @eq_refl (@Adjunction (Product_cat C C) C Prod (@product_diagonal_func C))
      (@one_cat_biproduct_adjunction C C1 Prod t A T0)
    : τ (@= (@Adjunction (Product_cat C C) C Prod (@product_diagonal_func C))
        (@one_cat_biproduct_adjunction C C1 Prod t A T0)
        (@one_cat_biproduct_adjunction C C1 Prod t A1 T0));

// Unit action is inherited from the same whole injections.
assert [C : Cat] (C1 : τ (IsNCat (cat_succ cat_zero) C))
  [Prod : τ (Functor (Product_cat C C) C)] [t : τ (Obj C)]
  (A : τ (@AdditiveCategory C Prod t)) (T0 : τ (@TerminalObject (Op_cat C) t))
  (x y : τ (Obj (Product_cat C C)))
  ⊢ @tapp1_func (Product_cat C C) C (@Product_projL_func C C) Prod x y
      (sigma_Fst (@unit_adj_transf (Product_cat C C) C Prod (@product_diagonal_func C)
        (@one_cat_biproduct_adjunction C C1 Prod t A T0)))
    ≡ @tapp1_func (Product_cat C C) C (@Product_projL_func C C) Prod x y
      (@one_cat_biproduct_inj1 C C1 Prod t A T0);
