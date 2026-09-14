/* Whole copairing and addition through the original biproduct adjunction.
   Whole functor composition and native mate cuts own all higher action. */
require open emdash.emdash3_2_one_cat_biproduct_adjunction;

// The native inverse mate is the whole copairing operation.
symbol one_cat_copair_family_func [B C : Cat] (C1 : τ (IsNCat (cat_succ cat_zero) C))
  [Prod : τ (Functor (Product_cat C C) C)] [t : τ (Obj C)]
  (A : τ (@AdditiveCategory C Prod t)) (T0 : τ (@TerminalObject (Op_cat C) t)) (X Y Z : τ (Functor B C))
  : τ (Functor (Product_cat (@Transf_cat B C X Z) (@Transf_cat B C Y Z)) (@Transf_cat B C (@fapp0 (Functor_cat B
    (Product_cat C C)) (Functor_cat B C) (@comp_cat_cov_func B (Product_cat C C) C Prod) (@Struct_sigma (Functor B C)
    (λ _ : τ (Functor B C), Functor B C) X Y)) Z))
≔ @one_cat_adjunction_family_untranspose_func B (Product_cat C C) C (@one_cat_product_category C C C1 C1) C1 Prod
  (@product_diagonal_func C) (@one_cat_biproduct_adjunction C C1 Prod t A T0) (@Struct_sigma (Functor B C) (λ _
  : τ (Functor B C), Functor B C) X Y) Z;

// Its inverse returns the original pair of whole transformations.
symbol one_cat_uncopair_family_func [B C : Cat] (C1 : τ (IsNCat (cat_succ cat_zero) C))
  [Prod : τ (Functor (Product_cat C C) C)] [t : τ (Obj C)]
  (A : τ (@AdditiveCategory C Prod t)) (T0 : τ (@TerminalObject (Op_cat C) t)) (X Y Z : τ (Functor B C))
  : τ (Functor (@Transf_cat B C (@fapp0 (Functor_cat B (Product_cat C C)) (Functor_cat B C) (@comp_cat_cov_func B
    (Product_cat C C) C Prod) (@Struct_sigma (Functor B C) (λ _ : τ (Functor B C), Functor B C) X Y)) Z) (Product_cat
    (@Transf_cat B C X Z) (@Transf_cat B C Y Z)))
≔ @one_cat_adjunction_family_transpose_func B (Product_cat C C) C (@one_cat_product_category C C C1 C1) C1 Prod
  (@product_diagonal_func C) (@one_cat_biproduct_adjunction C C1 Prod t A T0) (@Struct_sigma (Functor B C) (λ _
  : τ (Functor B C), Functor B C) X Y) Z;

// Whole copairing at its native input/output Hom annotations.
symbol one_cat_copair_family [B C : Cat] (C1 : τ (IsNCat (cat_succ cat_zero) C))
  [Prod : τ (Functor (Product_cat C C) C)] [t : τ (Obj C)]
  (A : τ (@AdditiveCategory C Prod t)) (T0 : τ (@TerminalObject (Op_cat C) t)) (X Y Z : τ (Functor B C))
  (f : τ (@Transf B C X Z)) (g : τ (@Transf B C Y Z))
  : τ (@Transf B C (@fapp0 (Functor_cat B (Product_cat C C)) (Functor_cat B C) (@comp_cat_cov_func B (Product_cat C C)
    C Prod) (@Struct_sigma (Functor B C) (λ _ : τ (Functor B C), Functor B C) X Y)) Z)
≔ @fapp0 (Hom_cat (Functor_cat B (Product_cat C C)) (@Struct_sigma (Functor B C) (λ _ : τ (Functor B C), Functor B C)
  X Y) (@fapp0 (Functor_cat B C) (Functor_cat B (Product_cat C C)) (@comp_cat_cov_func B C (Product_cat C C)
  (@product_diagonal_func C)) Z)) (@Transf_cat B C (@fapp0 (Functor_cat B (Product_cat C C)) (Functor_cat B C)
  (@comp_cat_cov_func B (Product_cat C C) C Prod) (@Struct_sigma (Functor B C) (λ _ : τ (Functor B C), Functor B C) X
  Y)) Z) (@one_cat_copair_family_func B C C1 Prod t A T0 X Y Z) (@Struct_sigma (@Transf B C X Z) (λ _ : τ
  (@Transf B C X Z), @Transf B C Y Z) f g);

// Native recovery retains the complete original pair and its higher action.
symbol one_cat_uncopair_family [B C : Cat] (C1 : τ (IsNCat (cat_succ cat_zero) C))
  [Prod : τ (Functor (Product_cat C C) C)] [t : τ (Obj C)]
  (A : τ (@AdditiveCategory C Prod t)) (T0 : τ (@TerminalObject (Op_cat C) t)) (X Y Z : τ (Functor B C))
  (h : τ (@Transf B C (@fapp0 (Functor_cat B (Product_cat C C)) (Functor_cat B C) (@comp_cat_cov_func B (Product_cat C
    C) C Prod) (@Struct_sigma (Functor B C) (λ _ : τ (Functor B C), Functor B C) X Y)) Z))
  : τ (Obj (Product_cat (@Transf_cat B C X Z) (@Transf_cat B C Y Z)))
≔ @fapp0 (@Transf_cat B C (@fapp0 (Functor_cat B (Product_cat C C)) (Functor_cat B C) (@comp_cat_cov_func B
  (Product_cat C C) C Prod) (@Struct_sigma (Functor B C) (λ _ : τ (Functor B C), Functor B C) X Y)) Z) (Hom_cat
  (Functor_cat B (Product_cat C C)) (@Struct_sigma (Functor B C) (λ _ : τ (Functor B C), Functor B C) X Y) (@fapp0
  (Functor_cat B C) (Functor_cat B (Product_cat C C)) (@comp_cat_cov_func B C (Product_cat C C)
  (@product_diagonal_func C)) Z)) (@one_cat_uncopair_family_func B C C1 Prod t A T0 X Y Z) h;
