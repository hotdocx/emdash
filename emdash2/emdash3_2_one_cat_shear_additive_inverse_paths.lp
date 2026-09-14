require open emdash.emdash3_2_one_cat_additive_family_bilinearity;
require open emdash.emdash3_2_one_cat_product_family_projection_paths;
require open emdash.emdash3_2_one_cat_negative_identity;

/* Whole additive inverse law from the original shear inverse and native product β. */

// The whole shear's coordinate is the original defining row.
symbol one_cat_shear_proj1_path [B C : Cat] (C1 : τ (IsNCat (cat_succ cat_zero) C)) [Prod : τ (Functor
  (Product_cat C C) C)] [t : τ (Obj C)] (A : τ (@AdditiveCategory C Prod t)) (T0 : τ (@TerminalObject (Op_cat C) t))
  (X : τ (Functor B C))
  : τ (@= (@Transf B C (@fapp0 (Functor_cat B (Product_cat C C)) (Functor_cat B C) (@comp_cat_cov_func B (Product_cat
  C C) C Prod) (@Struct_sigma (Functor B C) (λ _ : τ (Functor B C), Functor B C) X X)) X) (@comp_fapp0 (Functor_cat B
  C) (@fapp0 (Functor_cat B (Product_cat C C)) (Functor_cat B C) (@comp_cat_cov_func B (Product_cat C C) C Prod)
  (@Struct_sigma (Functor B C) (λ _ : τ (Functor B C), Functor B C) X X)) (@fapp0 (Functor_cat B (Product_cat C C))
  (Functor_cat B C) (@comp_cat_cov_func B (Product_cat C C) C Prod) (@Struct_sigma (Functor B C) (λ _ : τ (Functor B
  C), Functor B C) X X)) X (@one_cat_double_family_proj1 B C C1 Prod t A X) (@one_cat_shear_family B C C1 Prod t A T0
  X)) (@one_cat_double_family_proj1 B C C1 Prod t A X))
≔ @one_cat_product_family_pair_proj1_path B C C1 Prod (@additive_binary_products C Prod t A) (@fapp0 (Functor_cat B
  (Product_cat C C)) (Functor_cat B C) (@comp_cat_cov_func B (Product_cat C C) C Prod) (@Struct_sigma (Functor B C) (λ
  _ : τ (Functor B C), Functor B C) X X)) X X (@one_cat_double_family_proj1 B C C1 Prod t A X)
  (@one_cat_additive_family_add B C C1 Prod t A T0 (@fapp0 (Functor_cat B (Product_cat C C)) (Functor_cat B C)
  (@comp_cat_cov_func B (Product_cat C C) C Prod) (@Struct_sigma (Functor B C) (λ _ : τ (Functor B C), Functor B C) X
  X)) X (@one_cat_double_family_proj1 B C C1 Prod t A X) (@one_cat_double_family_proj2 B C C1 Prod t A X));

// The whole shear's coordinate is the original defining row.
symbol one_cat_shear_proj2_path [B C : Cat] (C1 : τ (IsNCat (cat_succ cat_zero) C)) [Prod : τ (Functor
  (Product_cat C C) C)] [t : τ (Obj C)] (A : τ (@AdditiveCategory C Prod t)) (T0 : τ (@TerminalObject (Op_cat C) t))
  (X : τ (Functor B C))
  : τ (@= (@Transf B C (@fapp0 (Functor_cat B (Product_cat C C)) (Functor_cat B C) (@comp_cat_cov_func B (Product_cat
  C C) C Prod) (@Struct_sigma (Functor B C) (λ _ : τ (Functor B C), Functor B C) X X)) X) (@comp_fapp0 (Functor_cat B
  C) (@fapp0 (Functor_cat B (Product_cat C C)) (Functor_cat B C) (@comp_cat_cov_func B (Product_cat C C) C Prod)
  (@Struct_sigma (Functor B C) (λ _ : τ (Functor B C), Functor B C) X X)) (@fapp0 (Functor_cat B (Product_cat C C))
  (Functor_cat B C) (@comp_cat_cov_func B (Product_cat C C) C Prod) (@Struct_sigma (Functor B C) (λ _ : τ (Functor B
  C), Functor B C) X X)) X (@one_cat_double_family_proj2 B C C1 Prod t A X) (@one_cat_shear_family B C C1 Prod t A T0
  X)) (@one_cat_additive_family_add B C C1 Prod t A T0 (@fapp0 (Functor_cat B (Product_cat C C)) (Functor_cat B C)
  (@comp_cat_cov_func B (Product_cat C C) C Prod) (@Struct_sigma (Functor B C) (λ _ : τ (Functor B C), Functor B C) X
  X)) X (@one_cat_double_family_proj1 B C C1 Prod t A X) (@one_cat_double_family_proj2 B C C1 Prod t A X)))
≔ @one_cat_product_family_pair_proj2_path B C C1 Prod (@additive_binary_products C Prod t A) (@fapp0 (Functor_cat B
  (Product_cat C C)) (Functor_cat B C) (@comp_cat_cov_func B (Product_cat C C) C Prod) (@Struct_sigma (Functor B C) (λ
  _ : τ (Functor B C), Functor B C) X X)) X X (@one_cat_double_family_proj1 B C C1 Prod t A X)
  (@one_cat_additive_family_add B C C1 Prod t A T0 (@fapp0 (Functor_cat B (Product_cat C C)) (Functor_cat B C)
  (@comp_cat_cov_func B (Product_cat C C) C Prod) (@Struct_sigma (Functor B C) (λ _ : τ (Functor B C), Functor B C) X
  X)) X (@one_cat_double_family_proj1 B C C1 Prod t A X) (@one_cat_double_family_proj2 B C C1 Prod t A X));

// The first inverse column is constructed from the existing whole inverse and injection.
symbol one_cat_shear_inverse_first_column [B C : Cat] (C1 : τ (IsNCat (cat_succ cat_zero) C)) [Prod : τ (Functor
  (Product_cat C C) C)] [t : τ (Obj C)] (A : τ (@AdditiveCategory C Prod t)) (T0 : τ (@TerminalObject (Op_cat C) t))
  (X : τ (Functor B C)) : τ (@Transf B C X (@fapp0 (Functor_cat B (Product_cat C C)) (Functor_cat B C)
  (@comp_cat_cov_func B (Product_cat C C) C Prod) (@Struct_sigma (Functor B C) (λ _ : τ (Functor B C), Functor B C) X
  X)))
≔ (@comp_fapp0 (Functor_cat B C) X (@fapp0 (Functor_cat B (Product_cat C C)) (Functor_cat B C) (@comp_cat_cov_func B
  (Product_cat C C) C Prod) (@Struct_sigma (Functor B C) (λ _ : τ (Functor B C), Functor B C) X X)) (@fapp0
  (Functor_cat B (Product_cat C C)) (Functor_cat B C) (@comp_cat_cov_func B (Product_cat C C) C Prod) (@Struct_sigma
  (Functor B C) (λ _ : τ (Functor B C), Functor B C) X X)) (@one_cat_shear_family_inverse B C C1 Prod t A T0 X)
  (@one_cat_double_family_inj1 B C C1 Prod t A T0 X));

// S∘(S⁻¹∘ι₁)=ι₁ follows from the same selected whole inverse law.
symbol one_cat_shear_inverse_first_column_path [B C : Cat] (C1 : τ (IsNCat (cat_succ cat_zero) C)) [Prod : τ
  (Functor (Product_cat C C) C)] [t : τ (Obj C)] (A : τ (@AdditiveCategory C Prod t)) (T0 : τ (@TerminalObject (Op_cat
  C) t)) (X : τ (Functor B C))
  : τ (@= (@Transf B C X (@fapp0 (Functor_cat B (Product_cat C C)) (Functor_cat B C) (@comp_cat_cov_func B
  (Product_cat C C) C Prod) (@Struct_sigma (Functor B C) (λ _ : τ (Functor B C), Functor B C) X X))) (@comp_fapp0
  (Functor_cat B C) X (@fapp0 (Functor_cat B (Product_cat C C)) (Functor_cat B C) (@comp_cat_cov_func B (Product_cat C
  C) C Prod) (@Struct_sigma (Functor B C) (λ _ : τ (Functor B C), Functor B C) X X)) (@fapp0 (Functor_cat B
  (Product_cat C C)) (Functor_cat B C) (@comp_cat_cov_func B (Product_cat C C) C Prod) (@Struct_sigma (Functor B C) (λ
  _ : τ (Functor B C), Functor B C) X X)) (@one_cat_shear_family B C C1 Prod t A T0 X)
  (@one_cat_shear_inverse_first_column B C C1 Prod t A T0 X)) (@one_cat_double_family_inj1 B C C1 Prod t A T0
  X))
≔ @eq_trans (@Transf B C X (@fapp0 (Functor_cat B (Product_cat C C)) (Functor_cat B C) (@comp_cat_cov_func B
  (Product_cat C C) C Prod) (@Struct_sigma (Functor B C) (λ _ : τ (Functor B C), Functor B C) X X))) (@comp_fapp0
  (Functor_cat B C) X (@fapp0 (Functor_cat B (Product_cat C C)) (Functor_cat B C) (@comp_cat_cov_func B (Product_cat C
  C) C Prod) (@Struct_sigma (Functor B C) (λ _ : τ (Functor B C), Functor B C) X X)) (@fapp0 (Functor_cat B
  (Product_cat C C)) (Functor_cat B C) (@comp_cat_cov_func B (Product_cat C C) C Prod) (@Struct_sigma (Functor B C) (λ
  _ : τ (Functor B C), Functor B C) X X)) (@one_cat_shear_family B C C1 Prod t A T0 X)
  (@one_cat_shear_inverse_first_column B C C1 Prod t A T0 X)) (@comp_fapp0 (Functor_cat B C) X (@fapp0
  (Functor_cat B (Product_cat C C)) (Functor_cat B C) (@comp_cat_cov_func B (Product_cat C C) C Prod) (@Struct_sigma
  (Functor B C) (λ _ : τ (Functor B C), Functor B C) X X)) (@fapp0 (Functor_cat B (Product_cat C C)) (Functor_cat B C)
  (@comp_cat_cov_func B (Product_cat C C) C Prod) (@Struct_sigma (Functor B C) (λ _ : τ (Functor B C), Functor B C) X
  X)) (@comp_fapp0 (Functor_cat B C) (@fapp0 (Functor_cat B (Product_cat C C)) (Functor_cat B C) (@comp_cat_cov_func B
  (Product_cat C C) C Prod) (@Struct_sigma (Functor B C) (λ _ : τ (Functor B C), Functor B C) X X)) (@fapp0
  (Functor_cat B (Product_cat C C)) (Functor_cat B C) (@comp_cat_cov_func B (Product_cat C C) C Prod) (@Struct_sigma
  (Functor B C) (λ _ : τ (Functor B C), Functor B C) X X)) (@fapp0 (Functor_cat B (Product_cat C C)) (Functor_cat B C)
  (@comp_cat_cov_func B (Product_cat C C) C Prod) (@Struct_sigma (Functor B C) (λ _ : τ (Functor B C), Functor B C) X
  X)) (@one_cat_shear_family B C C1 Prod t A T0 X) (@one_cat_shear_family_inverse B C C1 Prod t A T0 X))
  (@one_cat_double_family_inj1 B C C1 Prod t A T0 X)) (@one_cat_double_family_inj1 B C C1 Prod t A T0 X)
    (@comp_assoc (Functor_cat B C) X (@fapp0 (Functor_cat B (Product_cat C C)) (Functor_cat B C) (@comp_cat_cov_func B
  (Product_cat C C) C Prod) (@Struct_sigma (Functor B C) (λ _ : τ (Functor B C), Functor B C) X X)) (@fapp0
  (Functor_cat B (Product_cat C C)) (Functor_cat B C) (@comp_cat_cov_func B (Product_cat C C) C Prod) (@Struct_sigma
  (Functor B C) (λ _ : τ (Functor B C), Functor B C) X X)) (@fapp0 (Functor_cat B (Product_cat C C)) (Functor_cat B C)
  (@comp_cat_cov_func B (Product_cat C C) C Prod) (@Struct_sigma (Functor B C) (λ _ : τ (Functor B C), Functor B C) X
  X)) (@one_cat_shear_family B C C1 Prod t A T0 X) (@one_cat_shear_family_inverse B C C1 Prod t A T0 X)
  (@one_cat_double_family_inj1 B C C1 Prod t A T0 X))
    (@eq_ap (@Transf B C (@fapp0 (Functor_cat B (Product_cat C C)) (Functor_cat B C) (@comp_cat_cov_func B
  (Product_cat C C) C Prod) (@Struct_sigma (Functor B C) (λ _ : τ (Functor B C), Functor B C) X X)) (@fapp0
  (Functor_cat B (Product_cat C C)) (Functor_cat B C) (@comp_cat_cov_func B (Product_cat C C) C Prod) (@Struct_sigma
  (Functor B C) (λ _ : τ (Functor B C), Functor B C) X X))) (@Transf B C X (@fapp0 (Functor_cat B (Product_cat C C))
  (Functor_cat B C) (@comp_cat_cov_func B (Product_cat C C) C Prod) (@Struct_sigma (Functor B C) (λ _ : τ (Functor B
  C), Functor B C) X X)))
      (λ k : τ (@Transf B C (@fapp0 (Functor_cat B (Product_cat C C)) (Functor_cat B C) (@comp_cat_cov_func B
  (Product_cat C C) C Prod) (@Struct_sigma (Functor B C) (λ _ : τ (Functor B C), Functor B C) X X)) (@fapp0
  (Functor_cat B (Product_cat C C)) (Functor_cat B C) (@comp_cat_cov_func B (Product_cat C C) C Prod) (@Struct_sigma
  (Functor B C) (λ _ : τ (Functor B C), Functor B C) X X))), (@comp_fapp0 (Functor_cat B C) X (@fapp0 (Functor_cat B
  (Product_cat C C)) (Functor_cat B C) (@comp_cat_cov_func B (Product_cat C C) C Prod) (@Struct_sigma (Functor B C) (λ
  _ : τ (Functor B C), Functor B C) X X)) (@fapp0 (Functor_cat B (Product_cat C C)) (Functor_cat B C)
  (@comp_cat_cov_func B (Product_cat C C) C Prod) (@Struct_sigma (Functor B C) (λ _ : τ (Functor B C), Functor B C) X
  X)) k (@one_cat_double_family_inj1 B C C1 Prod t A T0 X)))
      (@comp_fapp0 (Functor_cat B C) (@fapp0 (Functor_cat B (Product_cat C C)) (Functor_cat B C) (@comp_cat_cov_func B
  (Product_cat C C) C Prod) (@Struct_sigma (Functor B C) (λ _ : τ (Functor B C), Functor B C) X X)) (@fapp0
  (Functor_cat B (Product_cat C C)) (Functor_cat B C) (@comp_cat_cov_func B (Product_cat C C) C Prod) (@Struct_sigma
  (Functor B C) (λ _ : τ (Functor B C), Functor B C) X X)) (@fapp0 (Functor_cat B (Product_cat C C)) (Functor_cat B C)
  (@comp_cat_cov_func B (Product_cat C C) C Prod) (@Struct_sigma (Functor B C) (λ _ : τ (Functor B C), Functor B C) X
  X)) (@one_cat_shear_family B C C1 Prod t A T0 X) (@one_cat_shear_family_inverse B C C1 Prod t A T0 X)) (@id
  (Functor_cat B C) (@fapp0 (Functor_cat B (Product_cat C C)) (Functor_cat B C) (@comp_cat_cov_func B (Product_cat C
  C) C Prod) (@Struct_sigma (Functor B C) (λ _ : τ (Functor B C), Functor B C) X X))) (@omega_equiv_left_as_right_law
  (Functor_cat B C) (@fapp0 (Functor_cat B (Product_cat C C)) (Functor_cat B C) (@comp_cat_cov_func B (Product_cat C
  C) C Prod) (@Struct_sigma (Functor B C) (λ _ : τ (Functor B C), Functor B C) X X)) (@fapp0 (Functor_cat B
  (Product_cat C C)) (Functor_cat B C) (@comp_cat_cov_func B (Product_cat C C) C Prod) (@Struct_sigma (Functor B C) (λ
  _ : τ (Functor B C), Functor B C) X X)) (@one_cat_shear_family B C C1 Prod t A T0 X) (@one_cat_shear_family_omega B
  C C1 Prod t A T0 X)));

// The original first row on the inverse column is reconstructed wholly.
symbol one_cat_shear_inverse_column_first_path [B C : Cat] (C1 : τ (IsNCat (cat_succ cat_zero) C)) [Prod : τ
  (Functor (Product_cat C C) C)] [t : τ (Obj C)] (A : τ (@AdditiveCategory C Prod t)) (T0 : τ (@TerminalObject (Op_cat
  C) t)) (X : τ (Functor B C))
  : τ (@= (@Transf B C X X) (@comp_fapp0 (Functor_cat B C) X (@fapp0 (Functor_cat B (Product_cat C C)) (Functor_cat B
  C) (@comp_cat_cov_func B (Product_cat C C) C Prod) (@Struct_sigma (Functor B C) (λ _ : τ (Functor B C), Functor B C)
  X X)) X (@one_cat_double_family_proj1 B C C1 Prod t A X) (@one_cat_shear_inverse_first_column B C C1 Prod t A
  T0 X)) (@id (Functor_cat B C) X))
≔ (@eq_trans (@Transf B C X X) (@comp_fapp0 (Functor_cat B C) X (@fapp0 (Functor_cat B (Product_cat C C)) (Functor_cat
  B C) (@comp_cat_cov_func B (Product_cat C C) C Prod) (@Struct_sigma (Functor B C) (λ _ : τ (Functor B C), Functor B
  C) X X)) X (@one_cat_double_family_proj1 B C C1 Prod t A X) (@one_cat_shear_inverse_first_column B C C1 Prod t
  A T0 X)) (@comp_fapp0 (Functor_cat B C) X (@fapp0 (Functor_cat B (Product_cat C C)) (Functor_cat B C)
  (@comp_cat_cov_func B (Product_cat C C) C Prod) (@Struct_sigma (Functor B C) (λ _ : τ (Functor B C), Functor B C) X
  X)) X (@comp_fapp0 (Functor_cat B C) (@fapp0 (Functor_cat B (Product_cat C C)) (Functor_cat B C) (@comp_cat_cov_func
  B (Product_cat C C) C Prod) (@Struct_sigma (Functor B C) (λ _ : τ (Functor B C), Functor B C) X X)) (@fapp0
  (Functor_cat B (Product_cat C C)) (Functor_cat B C) (@comp_cat_cov_func B (Product_cat C C) C Prod) (@Struct_sigma
  (Functor B C) (λ _ : τ (Functor B C), Functor B C) X X)) X (@one_cat_double_family_proj1 B C C1 Prod t A X)
  (@one_cat_shear_family B C C1 Prod t A T0 X)) (@one_cat_shear_inverse_first_column B C C1 Prod t A T0 X)) (@id
  (Functor_cat B C) X) (@eq_ap (@Transf B C (@fapp0 (Functor_cat B (Product_cat C C)) (Functor_cat B C)
  (@comp_cat_cov_func B (Product_cat C C) C Prod) (@Struct_sigma (Functor B C) (λ _ : τ (Functor B C), Functor B C) X
  X)) X) (@Transf B C X X) (λ k : τ (@Transf B C (@fapp0 (Functor_cat B (Product_cat C C)) (Functor_cat B C)
  (@comp_cat_cov_func B (Product_cat C C) C Prod) (@Struct_sigma (Functor B C) (λ _ : τ (Functor B C), Functor B C) X
  X)) X), (@comp_fapp0 (Functor_cat B C) X (@fapp0 (Functor_cat B (Product_cat C C)) (Functor_cat B C)
  (@comp_cat_cov_func B (Product_cat C C) C Prod) (@Struct_sigma (Functor B C) (λ _ : τ (Functor B C), Functor B C) X
  X)) X k (@one_cat_shear_inverse_first_column B C C1 Prod t A T0 X))) (@one_cat_double_family_proj1 B C C1 Prod
  t A X) (@comp_fapp0 (Functor_cat B C) (@fapp0 (Functor_cat B (Product_cat C C)) (Functor_cat B C)
  (@comp_cat_cov_func B (Product_cat C C) C Prod) (@Struct_sigma (Functor B C) (λ _ : τ (Functor B C), Functor B C) X
  X)) (@fapp0 (Functor_cat B (Product_cat C C)) (Functor_cat B C) (@comp_cat_cov_func B (Product_cat C C) C Prod)
  (@Struct_sigma (Functor B C) (λ _ : τ (Functor B C), Functor B C) X X)) X (@one_cat_double_family_proj1 B C C1 Prod
  t A X) (@one_cat_shear_family B C C1 Prod t A T0 X)) (@eq_sym (@Transf B C (@fapp0 (Functor_cat B (Product_cat C C))
  (Functor_cat B C) (@comp_cat_cov_func B (Product_cat C C) C Prod) (@Struct_sigma (Functor B C) (λ _ : τ (Functor B
  C), Functor B C) X X)) X) (@comp_fapp0 (Functor_cat B C) (@fapp0 (Functor_cat B (Product_cat C C)) (Functor_cat B C)
  (@comp_cat_cov_func B (Product_cat C C) C Prod) (@Struct_sigma (Functor B C) (λ _ : τ (Functor B C), Functor B C) X
  X)) (@fapp0 (Functor_cat B (Product_cat C C)) (Functor_cat B C) (@comp_cat_cov_func B (Product_cat C C) C Prod)
  (@Struct_sigma (Functor B C) (λ _ : τ (Functor B C), Functor B C) X X)) X (@one_cat_double_family_proj1 B C C1 Prod
  t A X) (@one_cat_shear_family B C C1 Prod t A T0 X)) (@one_cat_double_family_proj1 B C C1 Prod t A X)
  (@one_cat_shear_proj1_path B C C1 Prod t A T0 X))) (@eq_trans (@Transf B C X X) (@comp_fapp0 (Functor_cat B C)
  X (@fapp0 (Functor_cat B (Product_cat C C)) (Functor_cat B C) (@comp_cat_cov_func B (Product_cat C C) C Prod)
  (@Struct_sigma (Functor B C) (λ _ : τ (Functor B C), Functor B C) X X)) X (@comp_fapp0 (Functor_cat B C) (@fapp0
  (Functor_cat B (Product_cat C C)) (Functor_cat B C) (@comp_cat_cov_func B (Product_cat C C) C Prod) (@Struct_sigma
  (Functor B C) (λ _ : τ (Functor B C), Functor B C) X X)) (@fapp0 (Functor_cat B (Product_cat C C)) (Functor_cat B C)
  (@comp_cat_cov_func B (Product_cat C C) C Prod) (@Struct_sigma (Functor B C) (λ _ : τ (Functor B C), Functor B C) X
  X)) X (@one_cat_double_family_proj1 B C C1 Prod t A X) (@one_cat_shear_family B C C1 Prod t A T0 X))
  (@one_cat_shear_inverse_first_column B C C1 Prod t A T0 X)) (@comp_fapp0 (Functor_cat B C) X (@fapp0
  (Functor_cat B (Product_cat C C)) (Functor_cat B C) (@comp_cat_cov_func B (Product_cat C C) C Prod) (@Struct_sigma
  (Functor B C) (λ _ : τ (Functor B C), Functor B C) X X)) X (@one_cat_double_family_proj1 B C C1 Prod t A X)
  (@comp_fapp0 (Functor_cat B C) X (@fapp0 (Functor_cat B (Product_cat C C)) (Functor_cat B C) (@comp_cat_cov_func B
  (Product_cat C C) C Prod) (@Struct_sigma (Functor B C) (λ _ : τ (Functor B C), Functor B C) X X)) (@fapp0
  (Functor_cat B (Product_cat C C)) (Functor_cat B C) (@comp_cat_cov_func B (Product_cat C C) C Prod) (@Struct_sigma
  (Functor B C) (λ _ : τ (Functor B C), Functor B C) X X)) (@one_cat_shear_family B C C1 Prod t A T0 X)
  (@one_cat_shear_inverse_first_column B C C1 Prod t A T0 X))) (@id (Functor_cat B C) X) (@eq_sym (@Transf B C X
  X) (@comp_fapp0 (Functor_cat B C) X (@fapp0 (Functor_cat B (Product_cat C C)) (Functor_cat B C) (@comp_cat_cov_func
  B (Product_cat C C) C Prod) (@Struct_sigma (Functor B C) (λ _ : τ (Functor B C), Functor B C) X X)) X
  (@one_cat_double_family_proj1 B C C1 Prod t A X) (@comp_fapp0 (Functor_cat B C) X (@fapp0 (Functor_cat B
  (Product_cat C C)) (Functor_cat B C) (@comp_cat_cov_func B (Product_cat C C) C Prod) (@Struct_sigma (Functor B C) (λ
  _ : τ (Functor B C), Functor B C) X X)) (@fapp0 (Functor_cat B (Product_cat C C)) (Functor_cat B C)
  (@comp_cat_cov_func B (Product_cat C C) C Prod) (@Struct_sigma (Functor B C) (λ _ : τ (Functor B C), Functor B C) X
  X)) (@one_cat_shear_family B C C1 Prod t A T0 X) (@one_cat_shear_inverse_first_column B C C1 Prod t A T0 X)))
  (@comp_fapp0 (Functor_cat B C) X (@fapp0 (Functor_cat B (Product_cat C C)) (Functor_cat B C) (@comp_cat_cov_func B
  (Product_cat C C) C Prod) (@Struct_sigma (Functor B C) (λ _ : τ (Functor B C), Functor B C) X X)) X (@comp_fapp0
  (Functor_cat B C) (@fapp0 (Functor_cat B (Product_cat C C)) (Functor_cat B C) (@comp_cat_cov_func B (Product_cat C
  C) C Prod) (@Struct_sigma (Functor B C) (λ _ : τ (Functor B C), Functor B C) X X)) (@fapp0 (Functor_cat B
  (Product_cat C C)) (Functor_cat B C) (@comp_cat_cov_func B (Product_cat C C) C Prod) (@Struct_sigma (Functor B C) (λ
  _ : τ (Functor B C), Functor B C) X X)) X (@one_cat_double_family_proj1 B C C1 Prod t A X) (@one_cat_shear_family B
  C C1 Prod t A T0 X)) (@one_cat_shear_inverse_first_column B C C1 Prod t A T0 X)) (@comp_assoc (Functor_cat B
  C) X (@fapp0 (Functor_cat B (Product_cat C C)) (Functor_cat B C) (@comp_cat_cov_func B (Product_cat C C) C Prod)
  (@Struct_sigma (Functor B C) (λ _ : τ (Functor B C), Functor B C) X X)) (@fapp0 (Functor_cat B (Product_cat C C))
  (Functor_cat B C) (@comp_cat_cov_func B (Product_cat C C) C Prod) (@Struct_sigma (Functor B C) (λ _ : τ (Functor B
  C), Functor B C) X X)) X (@one_cat_double_family_proj1 B C C1 Prod t A X) (@one_cat_shear_family B C C1 Prod t A T0
  X) (@one_cat_shear_inverse_first_column B C C1 Prod t A T0 X))) (@eq_trans (@Transf B C X X) (@comp_fapp0
  (Functor_cat B C) X (@fapp0 (Functor_cat B (Product_cat C C)) (Functor_cat B C) (@comp_cat_cov_func B (Product_cat C
  C) C Prod) (@Struct_sigma (Functor B C) (λ _ : τ (Functor B C), Functor B C) X X)) X (@one_cat_double_family_proj1 B
  C C1 Prod t A X) (@comp_fapp0 (Functor_cat B C) X (@fapp0 (Functor_cat B (Product_cat C C)) (Functor_cat B C)
  (@comp_cat_cov_func B (Product_cat C C) C Prod) (@Struct_sigma (Functor B C) (λ _ : τ (Functor B C), Functor B C) X
  X)) (@fapp0 (Functor_cat B (Product_cat C C)) (Functor_cat B C) (@comp_cat_cov_func B (Product_cat C C) C Prod)
  (@Struct_sigma (Functor B C) (λ _ : τ (Functor B C), Functor B C) X X)) (@one_cat_shear_family B C C1 Prod t A T0 X)
  (@one_cat_shear_inverse_first_column B C C1 Prod t A T0 X))) (@comp_fapp0 (Functor_cat B C) X (@fapp0
  (Functor_cat B (Product_cat C C)) (Functor_cat B C) (@comp_cat_cov_func B (Product_cat C C) C Prod) (@Struct_sigma
  (Functor B C) (λ _ : τ (Functor B C), Functor B C) X X)) X (@one_cat_double_family_proj1 B C C1 Prod t A X)
  (@one_cat_double_family_inj1 B C C1 Prod t A T0 X)) (@id (Functor_cat B C) X) (@eq_ap (@Transf B C X (@fapp0
  (Functor_cat B (Product_cat C C)) (Functor_cat B C) (@comp_cat_cov_func B (Product_cat C C) C Prod) (@Struct_sigma
  (Functor B C) (λ _ : τ (Functor B C), Functor B C) X X))) (@Transf B C X X) (λ k : τ (@Transf B C X (@fapp0
  (Functor_cat B (Product_cat C C)) (Functor_cat B C) (@comp_cat_cov_func B (Product_cat C C) C Prod) (@Struct_sigma
  (Functor B C) (λ _ : τ (Functor B C), Functor B C) X X))), (@comp_fapp0 (Functor_cat B C) X (@fapp0 (Functor_cat B
  (Product_cat C C)) (Functor_cat B C) (@comp_cat_cov_func B (Product_cat C C) C Prod) (@Struct_sigma (Functor B C) (λ
  _ : τ (Functor B C), Functor B C) X X)) X (@one_cat_double_family_proj1 B C C1 Prod t A X) k)) (@comp_fapp0
  (Functor_cat B C) X (@fapp0 (Functor_cat B (Product_cat C C)) (Functor_cat B C) (@comp_cat_cov_func B (Product_cat C
  C) C Prod) (@Struct_sigma (Functor B C) (λ _ : τ (Functor B C), Functor B C) X X)) (@fapp0 (Functor_cat B
  (Product_cat C C)) (Functor_cat B C) (@comp_cat_cov_func B (Product_cat C C) C Prod) (@Struct_sigma (Functor B C) (λ
  _ : τ (Functor B C), Functor B C) X X)) (@one_cat_shear_family B C C1 Prod t A T0 X)
  (@one_cat_shear_inverse_first_column B C C1 Prod t A T0 X)) (@one_cat_double_family_inj1 B C C1 Prod t A T0 X)
  (@one_cat_shear_inverse_first_column_path B C C1 Prod t A T0 X)) (@one_cat_product_family_pair_proj1_path B C
  C1 Prod (@additive_binary_products C Prod t A) X X X (@id (Functor_cat B C) X) (@zero_arrow_family_zero_transf B C t
  (@additive_terminal_object C Prod t A) T0 X X)))));

// The original sum_zero row on the inverse column is reconstructed wholly.
symbol one_cat_shear_inverse_column_sum_zero_path [B C : Cat] (C1 : τ (IsNCat (cat_succ cat_zero) C)) [Prod : τ
  (Functor (Product_cat C C) C)] [t : τ (Obj C)] (A : τ (@AdditiveCategory C Prod t)) (T0 : τ (@TerminalObject (Op_cat
  C) t)) (X : τ (Functor B C))
  : τ (@= (@Transf B C X X) (@comp_fapp0 (Functor_cat B C) X (@fapp0 (Functor_cat B (Product_cat C C)) (Functor_cat B
  C) (@comp_cat_cov_func B (Product_cat C C) C Prod) (@Struct_sigma (Functor B C) (λ _ : τ (Functor B C), Functor B C)
  X X)) X (@one_cat_additive_family_add B C C1 Prod t A T0 (@fapp0 (Functor_cat B (Product_cat C C)) (Functor_cat B C)
  (@comp_cat_cov_func B (Product_cat C C) C Prod) (@Struct_sigma (Functor B C) (λ _ : τ (Functor B C), Functor B C) X
  X)) X (@one_cat_double_family_proj1 B C C1 Prod t A X) (@one_cat_double_family_proj2 B C C1 Prod t A X))
  (@one_cat_shear_inverse_first_column B C C1 Prod t A T0 X)) (@zero_arrow_family_zero_transf B C t
  (@additive_terminal_object C Prod t A) T0 X X))
≔ (@eq_trans (@Transf B C X X) (@comp_fapp0 (Functor_cat B C) X (@fapp0 (Functor_cat B (Product_cat C C)) (Functor_cat
  B C) (@comp_cat_cov_func B (Product_cat C C) C Prod) (@Struct_sigma (Functor B C) (λ _ : τ (Functor B C), Functor B
  C) X X)) X (@one_cat_additive_family_add B C C1 Prod t A T0 (@fapp0 (Functor_cat B (Product_cat C C)) (Functor_cat B
  C) (@comp_cat_cov_func B (Product_cat C C) C Prod) (@Struct_sigma (Functor B C) (λ _ : τ (Functor B C), Functor B C)
  X X)) X (@one_cat_double_family_proj1 B C C1 Prod t A X) (@one_cat_double_family_proj2 B C C1 Prod t A X))
  (@one_cat_shear_inverse_first_column B C C1 Prod t A T0 X)) (@comp_fapp0 (Functor_cat B C) X (@fapp0
  (Functor_cat B (Product_cat C C)) (Functor_cat B C) (@comp_cat_cov_func B (Product_cat C C) C Prod) (@Struct_sigma
  (Functor B C) (λ _ : τ (Functor B C), Functor B C) X X)) X (@comp_fapp0 (Functor_cat B C) (@fapp0 (Functor_cat B
  (Product_cat C C)) (Functor_cat B C) (@comp_cat_cov_func B (Product_cat C C) C Prod) (@Struct_sigma (Functor B C) (λ
  _ : τ (Functor B C), Functor B C) X X)) (@fapp0 (Functor_cat B (Product_cat C C)) (Functor_cat B C)
  (@comp_cat_cov_func B (Product_cat C C) C Prod) (@Struct_sigma (Functor B C) (λ _ : τ (Functor B C), Functor B C) X
  X)) X (@one_cat_double_family_proj2 B C C1 Prod t A X) (@one_cat_shear_family B C C1 Prod t A T0 X))
  (@one_cat_shear_inverse_first_column B C C1 Prod t A T0 X)) (@zero_arrow_family_zero_transf B C t
  (@additive_terminal_object C Prod t A) T0 X X) (@eq_ap (@Transf B C (@fapp0 (Functor_cat B (Product_cat C C))
  (Functor_cat B C) (@comp_cat_cov_func B (Product_cat C C) C Prod) (@Struct_sigma (Functor B C) (λ _ : τ (Functor B
  C), Functor B C) X X)) X) (@Transf B C X X) (λ k : τ (@Transf B C (@fapp0 (Functor_cat B (Product_cat C C))
  (Functor_cat B C) (@comp_cat_cov_func B (Product_cat C C) C Prod) (@Struct_sigma (Functor B C) (λ _ : τ (Functor B
  C), Functor B C) X X)) X), (@comp_fapp0 (Functor_cat B C) X (@fapp0 (Functor_cat B (Product_cat C C)) (Functor_cat B
  C) (@comp_cat_cov_func B (Product_cat C C) C Prod) (@Struct_sigma (Functor B C) (λ _ : τ (Functor B C), Functor B C)
  X X)) X k (@one_cat_shear_inverse_first_column B C C1 Prod t A T0 X))) (@one_cat_additive_family_add B C C1
  Prod t A T0 (@fapp0 (Functor_cat B (Product_cat C C)) (Functor_cat B C) (@comp_cat_cov_func B (Product_cat C C) C
  Prod) (@Struct_sigma (Functor B C) (λ _ : τ (Functor B C), Functor B C) X X)) X (@one_cat_double_family_proj1 B C C1
  Prod t A X) (@one_cat_double_family_proj2 B C C1 Prod t A X)) (@comp_fapp0 (Functor_cat B C) (@fapp0 (Functor_cat B
  (Product_cat C C)) (Functor_cat B C) (@comp_cat_cov_func B (Product_cat C C) C Prod) (@Struct_sigma (Functor B C) (λ
  _ : τ (Functor B C), Functor B C) X X)) (@fapp0 (Functor_cat B (Product_cat C C)) (Functor_cat B C)
  (@comp_cat_cov_func B (Product_cat C C) C Prod) (@Struct_sigma (Functor B C) (λ _ : τ (Functor B C), Functor B C) X
  X)) X (@one_cat_double_family_proj2 B C C1 Prod t A X) (@one_cat_shear_family B C C1 Prod t A T0 X)) (@eq_sym
  (@Transf B C (@fapp0 (Functor_cat B (Product_cat C C)) (Functor_cat B C) (@comp_cat_cov_func B (Product_cat C C) C
  Prod) (@Struct_sigma (Functor B C) (λ _ : τ (Functor B C), Functor B C) X X)) X) (@comp_fapp0 (Functor_cat B C)
  (@fapp0 (Functor_cat B (Product_cat C C)) (Functor_cat B C) (@comp_cat_cov_func B (Product_cat C C) C Prod)
  (@Struct_sigma (Functor B C) (λ _ : τ (Functor B C), Functor B C) X X)) (@fapp0 (Functor_cat B (Product_cat C C))
  (Functor_cat B C) (@comp_cat_cov_func B (Product_cat C C) C Prod) (@Struct_sigma (Functor B C) (λ _ : τ (Functor B
  C), Functor B C) X X)) X (@one_cat_double_family_proj2 B C C1 Prod t A X) (@one_cat_shear_family B C C1 Prod t A T0
  X)) (@one_cat_additive_family_add B C C1 Prod t A T0 (@fapp0 (Functor_cat B (Product_cat C C)) (Functor_cat B C)
  (@comp_cat_cov_func B (Product_cat C C) C Prod) (@Struct_sigma (Functor B C) (λ _ : τ (Functor B C), Functor B C) X
  X)) X (@one_cat_double_family_proj1 B C C1 Prod t A X) (@one_cat_double_family_proj2 B C C1 Prod t A X))
  (@one_cat_shear_proj2_path B C C1 Prod t A T0 X))) (@eq_trans (@Transf B C X X) (@comp_fapp0 (Functor_cat B C)
  X (@fapp0 (Functor_cat B (Product_cat C C)) (Functor_cat B C) (@comp_cat_cov_func B (Product_cat C C) C Prod)
  (@Struct_sigma (Functor B C) (λ _ : τ (Functor B C), Functor B C) X X)) X (@comp_fapp0 (Functor_cat B C) (@fapp0
  (Functor_cat B (Product_cat C C)) (Functor_cat B C) (@comp_cat_cov_func B (Product_cat C C) C Prod) (@Struct_sigma
  (Functor B C) (λ _ : τ (Functor B C), Functor B C) X X)) (@fapp0 (Functor_cat B (Product_cat C C)) (Functor_cat B C)
  (@comp_cat_cov_func B (Product_cat C C) C Prod) (@Struct_sigma (Functor B C) (λ _ : τ (Functor B C), Functor B C) X
  X)) X (@one_cat_double_family_proj2 B C C1 Prod t A X) (@one_cat_shear_family B C C1 Prod t A T0 X))
  (@one_cat_shear_inverse_first_column B C C1 Prod t A T0 X)) (@comp_fapp0 (Functor_cat B C) X (@fapp0
  (Functor_cat B (Product_cat C C)) (Functor_cat B C) (@comp_cat_cov_func B (Product_cat C C) C Prod) (@Struct_sigma
  (Functor B C) (λ _ : τ (Functor B C), Functor B C) X X)) X (@one_cat_double_family_proj2 B C C1 Prod t A X)
  (@comp_fapp0 (Functor_cat B C) X (@fapp0 (Functor_cat B (Product_cat C C)) (Functor_cat B C) (@comp_cat_cov_func B
  (Product_cat C C) C Prod) (@Struct_sigma (Functor B C) (λ _ : τ (Functor B C), Functor B C) X X)) (@fapp0
  (Functor_cat B (Product_cat C C)) (Functor_cat B C) (@comp_cat_cov_func B (Product_cat C C) C Prod) (@Struct_sigma
  (Functor B C) (λ _ : τ (Functor B C), Functor B C) X X)) (@one_cat_shear_family B C C1 Prod t A T0 X)
  (@one_cat_shear_inverse_first_column B C C1 Prod t A T0 X))) (@zero_arrow_family_zero_transf B C t
  (@additive_terminal_object C Prod t A) T0 X X) (@eq_sym (@Transf B C X X) (@comp_fapp0 (Functor_cat B C) X (@fapp0
  (Functor_cat B (Product_cat C C)) (Functor_cat B C) (@comp_cat_cov_func B (Product_cat C C) C Prod) (@Struct_sigma
  (Functor B C) (λ _ : τ (Functor B C), Functor B C) X X)) X (@one_cat_double_family_proj2 B C C1 Prod t A X)
  (@comp_fapp0 (Functor_cat B C) X (@fapp0 (Functor_cat B (Product_cat C C)) (Functor_cat B C) (@comp_cat_cov_func B
  (Product_cat C C) C Prod) (@Struct_sigma (Functor B C) (λ _ : τ (Functor B C), Functor B C) X X)) (@fapp0
  (Functor_cat B (Product_cat C C)) (Functor_cat B C) (@comp_cat_cov_func B (Product_cat C C) C Prod) (@Struct_sigma
  (Functor B C) (λ _ : τ (Functor B C), Functor B C) X X)) (@one_cat_shear_family B C C1 Prod t A T0 X)
  (@one_cat_shear_inverse_first_column B C C1 Prod t A T0 X))) (@comp_fapp0 (Functor_cat B C) X (@fapp0
  (Functor_cat B (Product_cat C C)) (Functor_cat B C) (@comp_cat_cov_func B (Product_cat C C) C Prod) (@Struct_sigma
  (Functor B C) (λ _ : τ (Functor B C), Functor B C) X X)) X (@comp_fapp0 (Functor_cat B C) (@fapp0 (Functor_cat B
  (Product_cat C C)) (Functor_cat B C) (@comp_cat_cov_func B (Product_cat C C) C Prod) (@Struct_sigma (Functor B C) (λ
  _ : τ (Functor B C), Functor B C) X X)) (@fapp0 (Functor_cat B (Product_cat C C)) (Functor_cat B C)
  (@comp_cat_cov_func B (Product_cat C C) C Prod) (@Struct_sigma (Functor B C) (λ _ : τ (Functor B C), Functor B C) X
  X)) X (@one_cat_double_family_proj2 B C C1 Prod t A X) (@one_cat_shear_family B C C1 Prod t A T0 X))
  (@one_cat_shear_inverse_first_column B C C1 Prod t A T0 X)) (@comp_assoc (Functor_cat B C) X (@fapp0
  (Functor_cat B (Product_cat C C)) (Functor_cat B C) (@comp_cat_cov_func B (Product_cat C C) C Prod) (@Struct_sigma
  (Functor B C) (λ _ : τ (Functor B C), Functor B C) X X)) (@fapp0 (Functor_cat B (Product_cat C C)) (Functor_cat B C)
  (@comp_cat_cov_func B (Product_cat C C) C Prod) (@Struct_sigma (Functor B C) (λ _ : τ (Functor B C), Functor B C) X
  X)) X (@one_cat_double_family_proj2 B C C1 Prod t A X) (@one_cat_shear_family B C C1 Prod t A T0 X)
  (@one_cat_shear_inverse_first_column B C C1 Prod t A T0 X))) (@eq_trans (@Transf B C X X) (@comp_fapp0
  (Functor_cat B C) X (@fapp0 (Functor_cat B (Product_cat C C)) (Functor_cat B C) (@comp_cat_cov_func B (Product_cat C
  C) C Prod) (@Struct_sigma (Functor B C) (λ _ : τ (Functor B C), Functor B C) X X)) X (@one_cat_double_family_proj2 B
  C C1 Prod t A X) (@comp_fapp0 (Functor_cat B C) X (@fapp0 (Functor_cat B (Product_cat C C)) (Functor_cat B C)
  (@comp_cat_cov_func B (Product_cat C C) C Prod) (@Struct_sigma (Functor B C) (λ _ : τ (Functor B C), Functor B C) X
  X)) (@fapp0 (Functor_cat B (Product_cat C C)) (Functor_cat B C) (@comp_cat_cov_func B (Product_cat C C) C Prod)
  (@Struct_sigma (Functor B C) (λ _ : τ (Functor B C), Functor B C) X X)) (@one_cat_shear_family B C C1 Prod t A T0 X)
  (@one_cat_shear_inverse_first_column B C C1 Prod t A T0 X))) (@comp_fapp0 (Functor_cat B C) X (@fapp0
  (Functor_cat B (Product_cat C C)) (Functor_cat B C) (@comp_cat_cov_func B (Product_cat C C) C Prod) (@Struct_sigma
  (Functor B C) (λ _ : τ (Functor B C), Functor B C) X X)) X (@one_cat_double_family_proj2 B C C1 Prod t A X)
  (@one_cat_double_family_inj1 B C C1 Prod t A T0 X)) (@zero_arrow_family_zero_transf B C t (@additive_terminal_object
  C Prod t A) T0 X X) (@eq_ap (@Transf B C X (@fapp0 (Functor_cat B (Product_cat C C)) (Functor_cat B C)
  (@comp_cat_cov_func B (Product_cat C C) C Prod) (@Struct_sigma (Functor B C) (λ _ : τ (Functor B C), Functor B C) X
  X))) (@Transf B C X X) (λ k : τ (@Transf B C X (@fapp0 (Functor_cat B (Product_cat C C)) (Functor_cat B C)
  (@comp_cat_cov_func B (Product_cat C C) C Prod) (@Struct_sigma (Functor B C) (λ _ : τ (Functor B C), Functor B C) X
  X))), (@comp_fapp0 (Functor_cat B C) X (@fapp0 (Functor_cat B (Product_cat C C)) (Functor_cat B C)
  (@comp_cat_cov_func B (Product_cat C C) C Prod) (@Struct_sigma (Functor B C) (λ _ : τ (Functor B C), Functor B C) X
  X)) X (@one_cat_double_family_proj2 B C C1 Prod t A X) k)) (@comp_fapp0 (Functor_cat B C) X (@fapp0 (Functor_cat B
  (Product_cat C C)) (Functor_cat B C) (@comp_cat_cov_func B (Product_cat C C) C Prod) (@Struct_sigma (Functor B C) (λ
  _ : τ (Functor B C), Functor B C) X X)) (@fapp0 (Functor_cat B (Product_cat C C)) (Functor_cat B C)
  (@comp_cat_cov_func B (Product_cat C C) C Prod) (@Struct_sigma (Functor B C) (λ _ : τ (Functor B C), Functor B C) X
  X)) (@one_cat_shear_family B C C1 Prod t A T0 X) (@one_cat_shear_inverse_first_column B C C1 Prod t A T0 X))
  (@one_cat_double_family_inj1 B C C1 Prod t A T0 X) (@one_cat_shear_inverse_first_column_path B C C1 Prod t A
  T0 X)) (@one_cat_product_family_pair_proj2_path B C C1 Prod (@additive_binary_products C Prod t A) X X X (@id
  (Functor_cat B C) X) (@zero_arrow_family_zero_transf B C t (@additive_terminal_object C Prod t A) T0 X X)))));

// id+N=0 is derived from the whole shear equations and whole bilinearity.
symbol one_cat_shear_negative_identity_add_path [B C : Cat] (C1 : τ (IsNCat (cat_succ cat_zero) C)) [Prod : τ
  (Functor (Product_cat C C) C)] [t : τ (Obj C)] (A : τ (@AdditiveCategory C Prod t)) (T0 : τ (@TerminalObject (Op_cat
  C) t)) (X : τ (Functor B C))
  : τ (@= (@Transf B C X X) (@one_cat_additive_family_add B C C1 Prod t A T0 X X (@id (Functor_cat B C) X)
  (@one_cat_shear_negative_identity_family B C C1 Prod t A T0 X)) (@zero_arrow_family_zero_transf B C t
  (@additive_terminal_object C Prod t A) T0 X X))
≔ (@eq_trans (@Transf B C X X) (@one_cat_additive_family_add B C C1 Prod t A T0 X X (@id (Functor_cat B C) X)
  (@one_cat_shear_negative_identity_family B C C1 Prod t A T0 X)) (@one_cat_additive_family_add B C C1 Prod t A T0 X X
  (@comp_fapp0 (Functor_cat B C) X (@fapp0 (Functor_cat B (Product_cat C C)) (Functor_cat B C) (@comp_cat_cov_func B
  (Product_cat C C) C Prod) (@Struct_sigma (Functor B C) (λ _ : τ (Functor B C), Functor B C) X X)) X
  (@one_cat_double_family_proj1 B C C1 Prod t A X) (@one_cat_shear_inverse_first_column B C C1 Prod t A T0 X))
  (@one_cat_shear_negative_identity_family B C C1 Prod t A T0 X)) (@zero_arrow_family_zero_transf B C t
  (@additive_terminal_object C Prod t A) T0 X X) (@eq_ap (@Transf B C X X) (@Transf B C X X) (λ k : τ (@Transf B C X
  X), (@one_cat_additive_family_add B C C1 Prod t A T0 X X k (@one_cat_shear_negative_identity_family B C C1 Prod t A
  T0 X))) (@id (Functor_cat B C) X) (@comp_fapp0 (Functor_cat B C) X (@fapp0 (Functor_cat B (Product_cat C C))
  (Functor_cat B C) (@comp_cat_cov_func B (Product_cat C C) C Prod) (@Struct_sigma (Functor B C) (λ _ : τ (Functor B
  C), Functor B C) X X)) X (@one_cat_double_family_proj1 B C C1 Prod t A X) (@one_cat_shear_inverse_first_column
  B C C1 Prod t A T0 X)) (@eq_sym (@Transf B C X X) (@comp_fapp0 (Functor_cat B C) X (@fapp0 (Functor_cat B
  (Product_cat C C)) (Functor_cat B C) (@comp_cat_cov_func B (Product_cat C C) C Prod) (@Struct_sigma (Functor B C) (λ
  _ : τ (Functor B C), Functor B C) X X)) X (@one_cat_double_family_proj1 B C C1 Prod t A X)
  (@one_cat_shear_inverse_first_column B C C1 Prod t A T0 X)) (@id (Functor_cat B C) X)
  (@one_cat_shear_inverse_column_first_path B C C1 Prod t A T0 X))) (@eq_trans (@Transf B C X X)
  (@one_cat_additive_family_add B C C1 Prod t A T0 X X (@comp_fapp0 (Functor_cat B C) X (@fapp0 (Functor_cat B
  (Product_cat C C)) (Functor_cat B C) (@comp_cat_cov_func B (Product_cat C C) C Prod) (@Struct_sigma (Functor B C) (λ
  _ : τ (Functor B C), Functor B C) X X)) X (@one_cat_double_family_proj1 B C C1 Prod t A X)
  (@one_cat_shear_inverse_first_column B C C1 Prod t A T0 X)) (@one_cat_shear_negative_identity_family B C C1
  Prod t A T0 X)) (@one_cat_additive_family_add B C C1 Prod t A T0 X X (@comp_fapp0 (Functor_cat B C) X (@fapp0
  (Functor_cat B (Product_cat C C)) (Functor_cat B C) (@comp_cat_cov_func B (Product_cat C C) C Prod) (@Struct_sigma
  (Functor B C) (λ _ : τ (Functor B C), Functor B C) X X)) X (@one_cat_double_family_proj1 B C C1 Prod t A X)
  (@one_cat_shear_inverse_first_column B C C1 Prod t A T0 X)) (@comp_fapp0 (Functor_cat B C) X (@fapp0
  (Functor_cat B (Product_cat C C)) (Functor_cat B C) (@comp_cat_cov_func B (Product_cat C C) C Prod) (@Struct_sigma
  (Functor B C) (λ _ : τ (Functor B C), Functor B C) X X)) X (@one_cat_double_family_proj2 B C C1 Prod t A X)
  (@one_cat_shear_inverse_first_column B C C1 Prod t A T0 X))) (@zero_arrow_family_zero_transf B C t
  (@additive_terminal_object C Prod t A) T0 X X) (@eq_ap (@Transf B C X X) (@Transf B C X X) (λ k : τ (@Transf B C X
  X), (@one_cat_additive_family_add B C C1 Prod t A T0 X X (@comp_fapp0 (Functor_cat B C) X (@fapp0 (Functor_cat B
  (Product_cat C C)) (Functor_cat B C) (@comp_cat_cov_func B (Product_cat C C) C Prod) (@Struct_sigma (Functor B C) (λ
  _ : τ (Functor B C), Functor B C) X X)) X (@one_cat_double_family_proj1 B C C1 Prod t A X)
  (@one_cat_shear_inverse_first_column B C C1 Prod t A T0 X)) k)) (@one_cat_shear_negative_identity_family B C
  C1 Prod t A T0 X) (@comp_fapp0 (Functor_cat B C) X (@fapp0 (Functor_cat B (Product_cat C C)) (Functor_cat B C)
  (@comp_cat_cov_func B (Product_cat C C) C Prod) (@Struct_sigma (Functor B C) (λ _ : τ (Functor B C), Functor B C) X
  X)) X (@one_cat_double_family_proj2 B C C1 Prod t A X) (@one_cat_shear_inverse_first_column B C C1 Prod t A T0
  X)) (@eq_sym (@Transf B C X X) (@comp_fapp0 (Functor_cat B C) X (@fapp0 (Functor_cat B (Product_cat C C))
  (Functor_cat B C) (@comp_cat_cov_func B (Product_cat C C) C Prod) (@Struct_sigma (Functor B C) (λ _ : τ (Functor B
  C), Functor B C) X X)) X (@one_cat_double_family_proj2 B C C1 Prod t A X) (@one_cat_shear_inverse_first_column
  B C C1 Prod t A T0 X)) (@one_cat_shear_negative_identity_family B C C1 Prod t A T0 X) (@comp_assoc (Functor_cat B C)
  X (@fapp0 (Functor_cat B (Product_cat C C)) (Functor_cat B C) (@comp_cat_cov_func B (Product_cat C C) C Prod)
  (@Struct_sigma (Functor B C) (λ _ : τ (Functor B C), Functor B C) X X)) (@fapp0 (Functor_cat B (Product_cat C C))
  (Functor_cat B C) (@comp_cat_cov_func B (Product_cat C C) C Prod) (@Struct_sigma (Functor B C) (λ _ : τ (Functor B
  C), Functor B C) X X)) X (@one_cat_double_family_proj2 B C C1 Prod t A X) (@one_cat_shear_family_inverse B C C1 Prod
  t A T0 X) (@one_cat_double_family_inj1 B C C1 Prod t A T0 X)))) (@eq_trans (@Transf B C X X)
  (@one_cat_additive_family_add B C C1 Prod t A T0 X X (@comp_fapp0 (Functor_cat B C) X (@fapp0 (Functor_cat B
  (Product_cat C C)) (Functor_cat B C) (@comp_cat_cov_func B (Product_cat C C) C Prod) (@Struct_sigma (Functor B C) (λ
  _ : τ (Functor B C), Functor B C) X X)) X (@one_cat_double_family_proj1 B C C1 Prod t A X)
  (@one_cat_shear_inverse_first_column B C C1 Prod t A T0 X)) (@comp_fapp0 (Functor_cat B C) X (@fapp0
  (Functor_cat B (Product_cat C C)) (Functor_cat B C) (@comp_cat_cov_func B (Product_cat C C) C Prod) (@Struct_sigma
  (Functor B C) (λ _ : τ (Functor B C), Functor B C) X X)) X (@one_cat_double_family_proj2 B C C1 Prod t A X)
  (@one_cat_shear_inverse_first_column B C C1 Prod t A T0 X))) (@comp_fapp0 (Functor_cat B C) X (@fapp0
  (Functor_cat B (Product_cat C C)) (Functor_cat B C) (@comp_cat_cov_func B (Product_cat C C) C Prod) (@Struct_sigma
  (Functor B C) (λ _ : τ (Functor B C), Functor B C) X X)) X (@one_cat_additive_family_add B C C1 Prod t A T0 (@fapp0
  (Functor_cat B (Product_cat C C)) (Functor_cat B C) (@comp_cat_cov_func B (Product_cat C C) C Prod) (@Struct_sigma
  (Functor B C) (λ _ : τ (Functor B C), Functor B C) X X)) X (@one_cat_double_family_proj1 B C C1 Prod t A X)
  (@one_cat_double_family_proj2 B C C1 Prod t A X)) (@one_cat_shear_inverse_first_column B C C1 Prod t A T0 X))
  (@zero_arrow_family_zero_transf B C t (@additive_terminal_object C Prod t A) T0 X X) (@eq_sym (@Transf B C X X)
  (@comp_fapp0 (Functor_cat B C) X (@fapp0 (Functor_cat B (Product_cat C C)) (Functor_cat B C) (@comp_cat_cov_func B
  (Product_cat C C) C Prod) (@Struct_sigma (Functor B C) (λ _ : τ (Functor B C), Functor B C) X X)) X
  (@one_cat_additive_family_add B C C1 Prod t A T0 (@fapp0 (Functor_cat B (Product_cat C C)) (Functor_cat B C)
  (@comp_cat_cov_func B (Product_cat C C) C Prod) (@Struct_sigma (Functor B C) (λ _ : τ (Functor B C), Functor B C) X
  X)) X (@one_cat_double_family_proj1 B C C1 Prod t A X) (@one_cat_double_family_proj2 B C C1 Prod t A X))
  (@one_cat_shear_inverse_first_column B C C1 Prod t A T0 X)) (@one_cat_additive_family_add B C C1 Prod t A T0 X
  X (@comp_fapp0 (Functor_cat B C) X (@fapp0 (Functor_cat B (Product_cat C C)) (Functor_cat B C) (@comp_cat_cov_func B
  (Product_cat C C) C Prod) (@Struct_sigma (Functor B C) (λ _ : τ (Functor B C), Functor B C) X X)) X
  (@one_cat_double_family_proj1 B C C1 Prod t A X) (@one_cat_shear_inverse_first_column B C C1 Prod t A T0 X))
  (@comp_fapp0 (Functor_cat B C) X (@fapp0 (Functor_cat B (Product_cat C C)) (Functor_cat B C) (@comp_cat_cov_func B
  (Product_cat C C) C Prod) (@Struct_sigma (Functor B C) (λ _ : τ (Functor B C), Functor B C) X X)) X
  (@one_cat_double_family_proj2 B C C1 Prod t A X) (@one_cat_shear_inverse_first_column B C C1 Prod t A T0 X)))
  (@one_cat_additive_family_precompose_path B C C1 Prod t A T0 X (@fapp0 (Functor_cat B (Product_cat C C))
  (Functor_cat B C) (@comp_cat_cov_func B (Product_cat C C) C Prod) (@Struct_sigma (Functor B C) (λ _ : τ (Functor B
  C), Functor B C) X X)) X (@one_cat_double_family_proj1 B C C1 Prod t A X) (@one_cat_double_family_proj2 B C C1 Prod
  t A X) (@one_cat_shear_inverse_first_column B C C1 Prod t A T0 X)))
  (@one_cat_shear_inverse_column_sum_zero_path B C C1 Prod t A T0 X))));

// Specialize at id_C to the original universal negative-identity transformation.
symbol one_cat_negative_identity_add_path [C : Cat] (C1 : τ (IsNCat (cat_succ cat_zero) C)) [Prod : τ (Functor
  (Product_cat C C) C)] [t : τ (Obj C)] (A : τ (@AdditiveCategory C Prod t)) (T0 : τ (@TerminalObject (Op_cat C) t))
  : τ (@= (@Transf C C (@id_func C) (@id_func C))
      (@one_cat_additive_family_add C C C1 Prod t A T0 (@id_func C) (@id_func C)
        (@id (Functor_cat C C) (@id_func C)) (@one_cat_negative_identity_transf C C1 Prod t A T0))
      (@zero_arrow_family_zero_transf C C t (@additive_terminal_object C Prod t A) T0 (@id_func C) (@id_func C)))
≔ @one_cat_shear_negative_identity_add_path C C C1 Prod t A T0 (@id_func C);
