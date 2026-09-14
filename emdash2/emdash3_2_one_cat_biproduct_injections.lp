/* Original whole biproduct injections through the existing product adjunction. */
require open emdash.emdash3_2_one_cat_product_families;
require open emdash.emdash3_2_one_cat_zero_family_paths;
require open emdash.emdash3_2_additive_categories;

// Use D=id_(C×C) as the actual mate endpoint; no paired-projection eta is needed.
symbol one_cat_biproduct_inj1 [C : Cat] (C1 : τ (IsNCat (cat_succ cat_zero) C))
  [Prod : τ (Functor (Product_cat C C) C)] [t : τ (Obj C)]
  (A : τ (@AdditiveCategory C Prod t)) (T0 : τ (@TerminalObject (Op_cat C) t))
  : τ (@Transf (Product_cat C C) C (@Product_projL_func C C) Prod)
≔ @fapp0
    (Hom_cat (Functor_cat (Product_cat C C) (Product_cat C C))
      (@fapp0 _ _ (@comp_cat_cov_func (Product_cat C C) C (Product_cat C C) (@product_diagonal_func C))
        (@Product_projL_func C C)) (@id_func (Product_cat C C)))
    (Hom_cat (Functor_cat (Product_cat C C) C) (@Product_projL_func C C)
      (@fapp0 _ _ (@comp_cat_cov_func (Product_cat C C) (Product_cat C C) C Prod)
        (@id_func (Product_cat C C))))
    (@one_cat_adjunction_family_transpose_func (Product_cat C C) C (Product_cat C C)
      C1 (@one_cat_product_category C C C1 C1) (@product_diagonal_func C) Prod
      (@one_cat_binary_product_adjunction C C1 Prod (@additive_binary_products C Prod t A))
      (@Product_projL_func C C) (@id_func (Product_cat C C)))
    (Struct_sigma (@id (Functor_cat (Product_cat C C) C) (@Product_projL_func C C))
      (@zero_arrow_family_zero_transf (Product_cat C C) C t (@additive_terminal_object C Prod t A) T0
        (@Product_projL_func C C) (@Product_projR_func C C)));

// The second injection uses the same Prod and original zero structures.
symbol one_cat_biproduct_inj2 [C : Cat] (C1 : τ (IsNCat (cat_succ cat_zero) C))
  [Prod : τ (Functor (Product_cat C C) C)] [t : τ (Obj C)]
  (A : τ (@AdditiveCategory C Prod t)) (T0 : τ (@TerminalObject (Op_cat C) t))
  : τ (@Transf (Product_cat C C) C (@Product_projR_func C C) Prod)
≔ @fapp0
    (Hom_cat (Functor_cat (Product_cat C C) (Product_cat C C))
      (@fapp0 _ _ (@comp_cat_cov_func (Product_cat C C) C (Product_cat C C) (@product_diagonal_func C))
        (@Product_projR_func C C)) (@id_func (Product_cat C C)))
    (Hom_cat (Functor_cat (Product_cat C C) C) (@Product_projR_func C C)
      (@fapp0 _ _ (@comp_cat_cov_func (Product_cat C C) (Product_cat C C) C Prod)
        (@id_func (Product_cat C C))))
    (@one_cat_adjunction_family_transpose_func (Product_cat C C) C (Product_cat C C)
      C1 (@one_cat_product_category C C C1 C1) (@product_diagonal_func C) Prod
      (@one_cat_binary_product_adjunction C C1 Prod (@additive_binary_products C Prod t A))
      (@Product_projR_func C C) (@id_func (Product_cat C C)))
    (Struct_sigma
      (@zero_arrow_family_zero_transf (Product_cat C C) C t (@additive_terminal_object C Prod t A) T0
        (@Product_projR_func C C) (@Product_projL_func C C))
      (@id (Functor_cat (Product_cat C C) C) (@Product_projR_func C C)));
