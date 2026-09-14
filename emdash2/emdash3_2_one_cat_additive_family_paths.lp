/* Addition is native copairing after the same selected product diagonal. */
require open emdash.emdash3_2_one_cat_copair_family_paths;
require open emdash.emdash3_2_one_cat_additive_families;

// Scalar readback of [f,g]∘Δ; bilinearity and original product β prove it.
symbol one_cat_copair_diagonal_path [C : Cat]
  [Prod : τ (Functor (Product_cat C C) C)] [t : τ (Obj C)] (A : τ (@AdditiveCategory C Prod t))
  (X Y : τ (Obj C)) (f g : τ (Hom C X Y))
  : τ (@= (Hom C X Y) (@comp_fapp0 C X (@fapp0 (Product_cat C C) C Prod (@Product_pair C C X X)) Y
  (@additive_copair_fapp0 C Prod t A X X Y f g) (@binary_products_pair_fapp0 C Prod (@additive_binary_products C Prod
  t A) X X X (@id C X) (@id C X))) (@preadditive_hom_add C (@additive_preadditive C Prod t A) X Y f g))
≔ @eq_trans (Hom C X Y) _ _ _
    ((@preadditive_comp_add_left_law C (@additive_preadditive C Prod t A)) X (@fapp0 (Product_cat C C) C Prod
  (@Product_pair C C X X)) Y
      (@comp_fapp0 C (@fapp0 (Product_cat C C) C Prod (@Product_pair C C X X)) X Y f (@binary_products_proj1_fapp0 C
  Prod (@additive_binary_products C Prod t A) X X)) (@comp_fapp0 C (@fapp0 (Product_cat C C) C Prod (@Product_pair C C
  X X)) X Y g (@binary_products_proj2_fapp0 C Prod (@additive_binary_products C Prod t A) X X))
  (@binary_products_pair_fapp0 C Prod (@additive_binary_products C Prod t A) X X X (@id C X) (@id C X)))
    (@additive_add_congr_path C Prod t A X Y _ f _ g
      (@eq_sym (Hom C X Y) _ _ (@comp_assoc C X (@fapp0 (Product_cat C C) C Prod (@Product_pair C C X X)) X Y f
  (@binary_products_proj1_fapp0 C Prod (@additive_binary_products C Prod t A) X X) (@binary_products_pair_fapp0 C Prod
  (@additive_binary_products C Prod t A) X X X (@id C X) (@id C X))))
      (@eq_sym (Hom C X Y) _ _ (@comp_assoc C X (@fapp0 (Product_cat C C) C Prod (@Product_pair C C X X)) X Y g
  (@binary_products_proj2_fapp0 C Prod (@additive_binary_products C Prod t A) X X) (@binary_products_pair_fapp0 C Prod
  (@additive_binary_products C Prod t A) X X X (@id C X) (@id C X)))));

// Native evaluation of the composite functor retains both original whole operations.
symbol one_cat_additive_family_add_formula_path [B C : Cat] (C1 : τ (IsNCat (cat_succ cat_zero) C))
  [Prod : τ (Functor (Product_cat C C) C)] [t : τ (Obj C)]
  (A : τ (@AdditiveCategory C Prod t)) (T0 : τ (@TerminalObject (Op_cat C) t))
  (X Y : τ (Functor B C)) (f g : τ (@Transf B C X Y))
  : τ (@= (@Transf B C X Y) (@one_cat_additive_family_add B C C1 Prod t A T0 X Y f g) (@comp_fapp0 (Functor_cat
  B C) X (@fapp0 (Functor_cat B (Product_cat C C)) (Functor_cat B C) (@comp_cat_cov_func B (Product_cat C C) C Prod)
  (@Struct_sigma (Functor B C) (λ _ : τ (Functor B C), Functor B C) X X)) Y (@one_cat_copair_family B C C1 Prod
  t A T0 X X Y f g) (@one_cat_product_family_pair B C C1 Prod (@additive_binary_products C Prod t A) X X X (@id
  (Functor_cat B C) X) (@id (Functor_cat B C) X))))
≔ @eq_refl (@Transf B C X Y) (@comp_fapp0 (Functor_cat B C) X (@fapp0 (Functor_cat B (Product_cat C C)) (Functor_cat B
  C) (@comp_cat_cov_func B (Product_cat C C) C Prod) (@Struct_sigma (Functor B C) (λ _ : τ (Functor B C), Functor B C)
  X X)) Y (@one_cat_copair_family B C C1 Prod t A T0 X X Y f g) (@one_cat_product_family_pair B C C1 Prod
  (@additive_binary_products C Prod t A) X X X (@id (Functor_cat B C) X) (@id (Functor_cat B C) X)));

// Components recover the original Hom addition; no pointwise square is an argument.
symbol one_cat_additive_family_add_component_path [B C : Cat] (C1 : τ (IsNCat (cat_succ cat_zero) C))
  [Prod : τ (Functor (Product_cat C C) C)] [t : τ (Obj C)]
  (A : τ (@AdditiveCategory C Prod t)) (T0 : τ (@TerminalObject (Op_cat C) t))
  (X Y : τ (Functor B C)) (f g : τ (@Transf B C X Y)) (b : τ (Obj B))
  : τ (@= (Hom C (@fapp0 B C X b) (@fapp0 B C Y b)) (@tapp0_fapp0 B C X Y b (@one_cat_additive_family_add B C C1
  Prod t A T0 X Y f g)) (@preadditive_hom_add C (@additive_preadditive C Prod t A) (@fapp0 B C X b) (@fapp0 B C Y b)
  (@tapp0_fapp0 B C X Y b f) (@tapp0_fapp0 B C X Y b g)))
≔ (@eq_trans (Hom C (@fapp0 B C X b) (@fapp0 B C Y b)) (@tapp0_fapp0 B C X Y b (@one_cat_additive_family_add B C
  C1 Prod t A T0 X Y f g)) (@comp_fapp0 C (@fapp0 B C X b) (@fapp0 (Product_cat C C) C Prod (@Product_pair C C (@fapp0
  B C X b) (@fapp0 B C X b))) (@fapp0 B C Y b) (@tapp0_fapp0 B C (@fapp0 (Functor_cat B (Product_cat C C))
  (Functor_cat B C) (@comp_cat_cov_func B (Product_cat C C) C Prod) (@Struct_sigma (Functor B C) (λ _ : τ (Functor B
  C), Functor B C) X X)) Y b (@one_cat_copair_family B C C1 Prod t A T0 X X Y f g)) (@tapp0_fapp0 B C X (@fapp0
  (Functor_cat B (Product_cat C C)) (Functor_cat B C) (@comp_cat_cov_func B (Product_cat C C) C Prod) (@Struct_sigma
  (Functor B C) (λ _ : τ (Functor B C), Functor B C) X X)) b (@one_cat_product_family_pair B C C1 Prod
  (@additive_binary_products C Prod t A) X X X (@id (Functor_cat B C) X) (@id (Functor_cat B C) X))))
  (@preadditive_hom_add C (@additive_preadditive C Prod t A) (@fapp0 B C X b) (@fapp0 B C Y b) (@tapp0_fapp0 B C X Y b
  f) (@tapp0_fapp0 B C X Y b g)) (@eq_ap (@Transf B C X Y) (Hom C (@fapp0 B C X b) (@fapp0 B C Y b)) (λ h : τ (@Transf
  B C X Y), @tapp0_fapp0 B C X Y b h) (@one_cat_additive_family_add B C C1 Prod t A T0 X Y f g) (@comp_fapp0
  (Functor_cat B C) X (@fapp0 (Functor_cat B (Product_cat C C)) (Functor_cat B C) (@comp_cat_cov_func B (Product_cat C
  C) C Prod) (@Struct_sigma (Functor B C) (λ _ : τ (Functor B C), Functor B C) X X)) Y (@one_cat_copair_family B
  C C1 Prod t A T0 X X Y f g) (@one_cat_product_family_pair B C C1 Prod (@additive_binary_products C Prod t A) X X X
  (@id (Functor_cat B C) X) (@id (Functor_cat B C) X))) (@one_cat_additive_family_add_formula_path B C C1 Prod t
  A T0 X Y f g)) (@eq_trans (Hom C (@fapp0 B C X b) (@fapp0 B C Y b)) (@comp_fapp0 C (@fapp0 B C X b) (@fapp0
  (Product_cat C C) C Prod (@Product_pair C C (@fapp0 B C X b) (@fapp0 B C X b))) (@fapp0 B C Y b) (@tapp0_fapp0 B C
  (@fapp0 (Functor_cat B (Product_cat C C)) (Functor_cat B C) (@comp_cat_cov_func B (Product_cat C C) C Prod)
  (@Struct_sigma (Functor B C) (λ _ : τ (Functor B C), Functor B C) X X)) Y b (@one_cat_copair_family B C C1
  Prod t A T0 X X Y f g)) (@tapp0_fapp0 B C X (@fapp0 (Functor_cat B (Product_cat C C)) (Functor_cat B C)
  (@comp_cat_cov_func B (Product_cat C C) C Prod) (@Struct_sigma (Functor B C) (λ _ : τ (Functor B C), Functor B C) X
  X)) b (@one_cat_product_family_pair B C C1 Prod (@additive_binary_products C Prod t A) X X X (@id (Functor_cat B C)
  X) (@id (Functor_cat B C) X)))) (@comp_fapp0 C (@fapp0 B C X b) (@fapp0 (Product_cat C C) C Prod (@Product_pair C C
  (@fapp0 B C X b) (@fapp0 B C X b))) (@fapp0 B C Y b) (@additive_copair_fapp0 C Prod t A (@fapp0 B C X b) (@fapp0 B C
  X b) (@fapp0 B C Y b) (@tapp0_fapp0 B C X Y b f) (@tapp0_fapp0 B C X Y b g)) (@tapp0_fapp0 B C X (@fapp0
  (Functor_cat B (Product_cat C C)) (Functor_cat B C) (@comp_cat_cov_func B (Product_cat C C) C Prod) (@Struct_sigma
  (Functor B C) (λ _ : τ (Functor B C), Functor B C) X X)) b (@one_cat_product_family_pair B C C1 Prod
  (@additive_binary_products C Prod t A) X X X (@id (Functor_cat B C) X) (@id (Functor_cat B C) X))))
  (@preadditive_hom_add C (@additive_preadditive C Prod t A) (@fapp0 B C X b) (@fapp0 B C Y b) (@tapp0_fapp0 B C X Y b
  f) (@tapp0_fapp0 B C X Y b g)) (@eq_ap (Hom C (@fapp0 (Product_cat C C) C Prod (@Product_pair C C (@fapp0 B C X b)
  (@fapp0 B C X b))) (@fapp0 B C Y b)) (Hom C (@fapp0 B C X b) (@fapp0 B C Y b)) (λ v : τ (Hom C (@fapp0 (Product_cat
  C C) C Prod (@Product_pair C C (@fapp0 B C X b) (@fapp0 B C X b))) (@fapp0 B C Y b)), (@comp_fapp0 C (@fapp0 B C X
  b) (@fapp0 (Product_cat C C) C Prod (@Product_pair C C (@fapp0 B C X b) (@fapp0 B C X b))) (@fapp0 B C Y b) v
  (@tapp0_fapp0 B C X (@fapp0 (Functor_cat B (Product_cat C C)) (Functor_cat B C) (@comp_cat_cov_func B (Product_cat C
  C) C Prod) (@Struct_sigma (Functor B C) (λ _ : τ (Functor B C), Functor B C) X X)) b (@one_cat_product_family_pair B
  C C1 Prod (@additive_binary_products C Prod t A) X X X (@id (Functor_cat B C) X) (@id (Functor_cat B C) X)))))
  (@tapp0_fapp0 B C (@fapp0 (Functor_cat B (Product_cat C C)) (Functor_cat B C) (@comp_cat_cov_func B (Product_cat C
  C) C Prod) (@Struct_sigma (Functor B C) (λ _ : τ (Functor B C), Functor B C) X X)) Y b (@one_cat_copair_family
  B C C1 Prod t A T0 X X Y f g)) (@additive_copair_fapp0 C Prod t A (@fapp0 B C X b) (@fapp0 B C X b) (@fapp0 B C Y b)
  (@tapp0_fapp0 B C X Y b f) (@tapp0_fapp0 B C X Y b g)) (@one_cat_copair_family_component_path B C C1 Prod t A
  T0 X X Y f g b)) (@eq_trans (Hom C (@fapp0 B C X b) (@fapp0 B C Y b)) (@comp_fapp0 C (@fapp0 B C X b) (@fapp0
  (Product_cat C C) C Prod (@Product_pair C C (@fapp0 B C X b) (@fapp0 B C X b))) (@fapp0 B C Y b)
  (@additive_copair_fapp0 C Prod t A (@fapp0 B C X b) (@fapp0 B C X b) (@fapp0 B C Y b) (@tapp0_fapp0 B C X Y b f)
  (@tapp0_fapp0 B C X Y b g)) (@tapp0_fapp0 B C X (@fapp0 (Functor_cat B (Product_cat C C)) (Functor_cat B C)
  (@comp_cat_cov_func B (Product_cat C C) C Prod) (@Struct_sigma (Functor B C) (λ _ : τ (Functor B C), Functor B C) X
  X)) b (@one_cat_product_family_pair B C C1 Prod (@additive_binary_products C Prod t A) X X X (@id (Functor_cat B C)
  X) (@id (Functor_cat B C) X)))) (@comp_fapp0 C (@fapp0 B C X b) (@fapp0 (Product_cat C C) C Prod (@Product_pair C C
  (@fapp0 B C X b) (@fapp0 B C X b))) (@fapp0 B C Y b) (@additive_copair_fapp0 C Prod t A (@fapp0 B C X b) (@fapp0 B C
  X b) (@fapp0 B C Y b) (@tapp0_fapp0 B C X Y b f) (@tapp0_fapp0 B C X Y b g)) (@binary_products_pair_fapp0 C Prod
  (@additive_binary_products C Prod t A) (@fapp0 B C X b) (@fapp0 B C X b) (@fapp0 B C X b) (@id C (@fapp0 B C X b))
  (@id C (@fapp0 B C X b)))) (@preadditive_hom_add C (@additive_preadditive C Prod t A) (@fapp0 B C X b) (@fapp0 B C Y
  b) (@tapp0_fapp0 B C X Y b f) (@tapp0_fapp0 B C X Y b g)) (@eq_ap (Hom C (@fapp0 B C X b) (@fapp0 (Product_cat C C)
  C Prod (@Product_pair C C (@fapp0 B C X b) (@fapp0 B C X b)))) (Hom C (@fapp0 B C X b) (@fapp0 B C Y b)) (λ v : τ
  (Hom C (@fapp0 B C X b) (@fapp0 (Product_cat C C) C Prod (@Product_pair C C (@fapp0 B C X b) (@fapp0 B C X b)))),
  (@comp_fapp0 C (@fapp0 B C X b) (@fapp0 (Product_cat C C) C Prod (@Product_pair C C (@fapp0 B C X b) (@fapp0 B C X
  b))) (@fapp0 B C Y b) (@additive_copair_fapp0 C Prod t A (@fapp0 B C X b) (@fapp0 B C X b) (@fapp0 B C Y b)
  (@tapp0_fapp0 B C X Y b f) (@tapp0_fapp0 B C X Y b g)) v)) (@tapp0_fapp0 B C X (@fapp0 (Functor_cat B (Product_cat C
  C)) (Functor_cat B C) (@comp_cat_cov_func B (Product_cat C C) C Prod) (@Struct_sigma (Functor B C) (λ _ : τ (Functor
  B C), Functor B C) X X)) b (@one_cat_product_family_pair B C C1 Prod (@additive_binary_products C Prod t A) X X X
  (@id (Functor_cat B C) X) (@id (Functor_cat B C) X))) (@binary_products_pair_fapp0 C Prod (@additive_binary_products
  C Prod t A) (@fapp0 B C X b) (@fapp0 B C X b) (@fapp0 B C X b) (@id C (@fapp0 B C X b)) (@id C (@fapp0 B C X b)))
  (@one_cat_product_family_pair_component_path B C C1 Prod (@additive_binary_products C Prod t A) X X X (@id
  (Functor_cat B C) X) (@id (Functor_cat B C) X) b)) (@one_cat_copair_diagonal_path C Prod t A (@fapp0 B C X b)
  (@fapp0 B C Y b) (@tapp0_fapp0 B C X Y b f) (@tapp0_fapp0 B C X Y b g)))));
