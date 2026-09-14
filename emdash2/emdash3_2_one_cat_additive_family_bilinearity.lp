require open emdash.emdash3_2_one_cat_biproduct_family_distribution;

/* Whole addition is preserved by postcomposition, through native copairing. */

// h∘(f+g)=(h∘f)+(h∘g); no component equality assembly is used.
symbol one_cat_additive_family_postcompose_path [B C : Cat] (C1 : τ (IsNCat (cat_succ cat_zero) C)) [Prod : τ
  (Functor (Product_cat C C) C)] [t : τ (Obj C)] (A : τ (@AdditiveCategory C Prod t)) (T0 : τ (@TerminalObject (Op_cat
  C) t)) (X Y Z : τ (Functor B C))
  (f g : τ (@Transf B C X Y)) (h : τ (@Transf B C Y Z))
  : τ (@= (@Transf B C X Z) (@comp_fapp0 (Functor_cat B C) X Y Z h (@one_cat_additive_family_add B C C1 Prod t A T0 X
  Y f g)) (@one_cat_additive_family_add B C C1 Prod t A T0 X Z (@comp_fapp0 (Functor_cat B C) X Y Z h f) (@comp_fapp0
  (Functor_cat B C) X Y Z h g)))
≔ (@eq_trans (@Transf B C X Z) (@comp_fapp0 (Functor_cat B C) X Y Z h (@one_cat_additive_family_add B C C1 Prod t A T0
  X Y f g)) (@comp_fapp0 (Functor_cat B C) X Y Z h (@comp_fapp0 (Functor_cat B C) X (@fapp0 (Functor_cat B
  (Product_cat C C)) (Functor_cat B C) (@comp_cat_cov_func B (Product_cat C C) C Prod) (@Struct_sigma (Functor B C) (λ
  _ : τ (Functor B C), Functor B C) X X)) Y (@one_cat_copair_family B C C1 Prod t A T0 X X Y f g)
  (@one_cat_product_family_pair B C C1 Prod (@additive_binary_products C Prod t A) X X X (@id (Functor_cat B C) X)
  (@id (Functor_cat B C) X)))) (@one_cat_additive_family_add B C C1 Prod t A T0 X Z (@comp_fapp0 (Functor_cat B C) X Y
  Z h f) (@comp_fapp0 (Functor_cat B C) X Y Z h g)) (@eq_ap (@Transf B C X Y) (@Transf B C X Z) (λ k : τ (@Transf B C
  X Y), (@comp_fapp0 (Functor_cat B C) X Y Z h k)) (@one_cat_additive_family_add B C C1 Prod t A T0 X Y f g)
  (@comp_fapp0 (Functor_cat B C) X (@fapp0 (Functor_cat B (Product_cat C C)) (Functor_cat B C) (@comp_cat_cov_func B
  (Product_cat C C) C Prod) (@Struct_sigma (Functor B C) (λ _ : τ (Functor B C), Functor B C) X X)) Y
  (@one_cat_copair_family B C C1 Prod t A T0 X X Y f g) (@one_cat_product_family_pair B C C1 Prod
  (@additive_binary_products C Prod t A) X X X (@id (Functor_cat B C) X) (@id (Functor_cat B C) X)))
  (@one_cat_additive_family_add_formula_path B C C1 Prod t A T0 X Y f g)) (@eq_trans (@Transf B C X Z) (@comp_fapp0
  (Functor_cat B C) X Y Z h (@comp_fapp0 (Functor_cat B C) X (@fapp0 (Functor_cat B (Product_cat C C)) (Functor_cat B
  C) (@comp_cat_cov_func B (Product_cat C C) C Prod) (@Struct_sigma (Functor B C) (λ _ : τ (Functor B C), Functor B C)
  X X)) Y (@one_cat_copair_family B C C1 Prod t A T0 X X Y f g) (@one_cat_product_family_pair B C C1 Prod
  (@additive_binary_products C Prod t A) X X X (@id (Functor_cat B C) X) (@id (Functor_cat B C) X)))) (@comp_fapp0
  (Functor_cat B C) X (@fapp0 (Functor_cat B (Product_cat C C)) (Functor_cat B C) (@comp_cat_cov_func B (Product_cat C
  C) C Prod) (@Struct_sigma (Functor B C) (λ _ : τ (Functor B C), Functor B C) X X)) Z (@comp_fapp0 (Functor_cat B C)
  (@fapp0 (Functor_cat B (Product_cat C C)) (Functor_cat B C) (@comp_cat_cov_func B (Product_cat C C) C Prod)
  (@Struct_sigma (Functor B C) (λ _ : τ (Functor B C), Functor B C) X X)) Y Z h (@one_cat_copair_family B C C1 Prod t
  A T0 X X Y f g)) (@one_cat_product_family_pair B C C1 Prod (@additive_binary_products C Prod t A) X X X (@id
  (Functor_cat B C) X) (@id (Functor_cat B C) X))) (@one_cat_additive_family_add B C C1 Prod t A T0 X Z (@comp_fapp0
  (Functor_cat B C) X Y Z h f) (@comp_fapp0 (Functor_cat B C) X Y Z h g)) (@comp_assoc (Functor_cat B C) X (@fapp0
  (Functor_cat B (Product_cat C C)) (Functor_cat B C) (@comp_cat_cov_func B (Product_cat C C) C Prod) (@Struct_sigma
  (Functor B C) (λ _ : τ (Functor B C), Functor B C) X X)) Y Z h (@one_cat_copair_family B C C1 Prod t A T0 X X Y f g)
  (@one_cat_product_family_pair B C C1 Prod (@additive_binary_products C Prod t A) X X X (@id (Functor_cat B C) X)
  (@id (Functor_cat B C) X))) (@eq_trans (@Transf B C X Z) (@comp_fapp0 (Functor_cat B C) X (@fapp0 (Functor_cat B
  (Product_cat C C)) (Functor_cat B C) (@comp_cat_cov_func B (Product_cat C C) C Prod) (@Struct_sigma (Functor B C) (λ
  _ : τ (Functor B C), Functor B C) X X)) Z (@comp_fapp0 (Functor_cat B C) (@fapp0 (Functor_cat B (Product_cat C C))
  (Functor_cat B C) (@comp_cat_cov_func B (Product_cat C C) C Prod) (@Struct_sigma (Functor B C) (λ _ : τ (Functor B
  C), Functor B C) X X)) Y Z h (@one_cat_copair_family B C C1 Prod t A T0 X X Y f g)) (@one_cat_product_family_pair B
  C C1 Prod (@additive_binary_products C Prod t A) X X X (@id (Functor_cat B C) X) (@id (Functor_cat B C) X)))
  (@comp_fapp0 (Functor_cat B C) X (@fapp0 (Functor_cat B (Product_cat C C)) (Functor_cat B C) (@comp_cat_cov_func B
  (Product_cat C C) C Prod) (@Struct_sigma (Functor B C) (λ _ : τ (Functor B C), Functor B C) X X)) Z
  (@one_cat_copair_family B C C1 Prod t A T0 X X Z (@comp_fapp0 (Functor_cat B C) X Y Z h f) (@comp_fapp0 (Functor_cat
  B C) X Y Z h g)) (@one_cat_product_family_pair B C C1 Prod (@additive_binary_products C Prod t A) X X X (@id
  (Functor_cat B C) X) (@id (Functor_cat B C) X))) (@one_cat_additive_family_add B C C1 Prod t A T0 X Z (@comp_fapp0
  (Functor_cat B C) X Y Z h f) (@comp_fapp0 (Functor_cat B C) X Y Z h g)) (@eq_ap (@Transf B C (@fapp0 (Functor_cat B
  (Product_cat C C)) (Functor_cat B C) (@comp_cat_cov_func B (Product_cat C C) C Prod) (@Struct_sigma (Functor B C) (λ
  _ : τ (Functor B C), Functor B C) X X)) Z) (@Transf B C X Z) (λ k : τ (@Transf B C (@fapp0 (Functor_cat B
  (Product_cat C C)) (Functor_cat B C) (@comp_cat_cov_func B (Product_cat C C) C Prod) (@Struct_sigma (Functor B C) (λ
  _ : τ (Functor B C), Functor B C) X X)) Z), (@comp_fapp0 (Functor_cat B C) X (@fapp0 (Functor_cat B (Product_cat C
  C)) (Functor_cat B C) (@comp_cat_cov_func B (Product_cat C C) C Prod) (@Struct_sigma (Functor B C) (λ _ : τ (Functor
  B C), Functor B C) X X)) Z k (@one_cat_product_family_pair B C C1 Prod (@additive_binary_products C Prod t A) X X X
  (@id (Functor_cat B C) X) (@id (Functor_cat B C) X)))) (@comp_fapp0 (Functor_cat B C) (@fapp0 (Functor_cat B
  (Product_cat C C)) (Functor_cat B C) (@comp_cat_cov_func B (Product_cat C C) C Prod) (@Struct_sigma (Functor B C) (λ
  _ : τ (Functor B C), Functor B C) X X)) Y Z h (@one_cat_copair_family B C C1 Prod t A T0 X X Y f g))
  (@one_cat_copair_family B C C1 Prod t A T0 X X Z (@comp_fapp0 (Functor_cat B C) X Y Z h f) (@comp_fapp0 (Functor_cat
  B C) X Y Z h g)) (@one_cat_copair_postcompose_path B C C1 Prod t A T0 X X Y Z f g h)) (@eq_sym (@Transf B C X
  Z) (@one_cat_additive_family_add B C C1 Prod t A T0 X Z (@comp_fapp0 (Functor_cat B C) X Y Z h f) (@comp_fapp0
  (Functor_cat B C) X Y Z h g)) (@comp_fapp0 (Functor_cat B C) X (@fapp0 (Functor_cat B (Product_cat C C))
  (Functor_cat B C) (@comp_cat_cov_func B (Product_cat C C) C Prod) (@Struct_sigma (Functor B C) (λ _ : τ (Functor B
  C), Functor B C) X X)) Z (@one_cat_copair_family B C C1 Prod t A T0 X X Z (@comp_fapp0 (Functor_cat B C) X Y Z h f)
  (@comp_fapp0 (Functor_cat B C) X Y Z h g)) (@one_cat_product_family_pair B C C1 Prod (@additive_binary_products C
  Prod t A) X X X (@id (Functor_cat B C) X) (@id (Functor_cat B C) X))) (@one_cat_additive_family_add_formula_path B C
  C1 Prod t A T0 X Z (@comp_fapp0 (Functor_cat B C) X Y Z h f) (@comp_fapp0 (Functor_cat B C) X Y Z h g))))));

/* Whole diagonal naturality and precomposition distributivity at the original products. */

// Original diagonal pairing commutes with the original product-map action.
symbol one_cat_product_diagonal_naturality_path [B C : Cat] (C1 : τ (IsNCat (cat_succ cat_zero) C)) [Prod : τ
  (Functor (Product_cat C C) C)] (BP : τ (@BinaryProducts C Prod)) (W X : τ (Functor B C)) (h : τ (@Transf B C W X))
  : τ (@= (@Transf B C W (@fapp0 (Functor_cat B (Product_cat C C)) (Functor_cat B C) (@comp_cat_cov_func B
  (Product_cat C C) C Prod) (@Struct_sigma (Functor B C) (λ _ : τ (Functor B C), Functor B C) X X))) (@comp_fapp0
  (Functor_cat B C) W X (@fapp0 (Functor_cat B (Product_cat C C)) (Functor_cat B C) (@comp_cat_cov_func B (Product_cat
  C C) C Prod) (@Struct_sigma (Functor B C) (λ _ : τ (Functor B C), Functor B C) X X)) (@one_cat_product_family_pair B
  C C1 Prod BP X X X (@id (Functor_cat B C) X) (@id (Functor_cat B C) X)) h) (@comp_fapp0 (Functor_cat B C) W (@fapp0
  (Functor_cat B (Product_cat C C)) (Functor_cat B C) (@comp_cat_cov_func B (Product_cat C C) C Prod) (@Struct_sigma
  (Functor B C) (λ _ : τ (Functor B C), Functor B C) W W)) (@fapp0 (Functor_cat B (Product_cat C C)) (Functor_cat B C)
  (@comp_cat_cov_func B (Product_cat C C) C Prod) (@Struct_sigma (Functor B C) (λ _ : τ (Functor B C), Functor B C) X
  X)) (@product_family_map B C Prod W W X X h h) (@one_cat_product_family_pair B C C1 Prod BP W W W (@id
  (Functor_cat B C) W) (@id (Functor_cat B C) W))))
≔ (@eq_trans (@Transf B C W (@fapp0 (Functor_cat B (Product_cat C C)) (Functor_cat B C) (@comp_cat_cov_func B
  (Product_cat C C) C Prod) (@Struct_sigma (Functor B C) (λ _ : τ (Functor B C), Functor B C) X X))) (@comp_fapp0
  (Functor_cat B C) W X (@fapp0 (Functor_cat B (Product_cat C C)) (Functor_cat B C) (@comp_cat_cov_func B (Product_cat
  C C) C Prod) (@Struct_sigma (Functor B C) (λ _ : τ (Functor B C), Functor B C) X X)) (@one_cat_product_family_pair B
  C C1 Prod BP X X X (@id (Functor_cat B C) X) (@id (Functor_cat B C) X)) h) (@one_cat_product_family_pair B C C1 Prod
  BP W X X h h) (@comp_fapp0 (Functor_cat B C) W (@fapp0 (Functor_cat B (Product_cat C C)) (Functor_cat B C)
  (@comp_cat_cov_func B (Product_cat C C) C Prod) (@Struct_sigma (Functor B C) (λ _ : τ (Functor B C), Functor B C) W
  W)) (@fapp0 (Functor_cat B (Product_cat C C)) (Functor_cat B C) (@comp_cat_cov_func B (Product_cat C C) C Prod)
  (@Struct_sigma (Functor B C) (λ _ : τ (Functor B C), Functor B C) X X)) (@product_family_map B C Prod W W X X
  h h) (@one_cat_product_family_pair B C C1 Prod BP W W W (@id (Functor_cat B C) W) (@id (Functor_cat B C) W)))
  (@one_cat_product_pair_precompose_path B C C1 Prod BP W X X X h (@id (Functor_cat B C) X) (@id (Functor_cat B
  C) X)) (@eq_sym (@Transf B C W (@fapp0 (Functor_cat B (Product_cat C C)) (Functor_cat B C) (@comp_cat_cov_func B
  (Product_cat C C) C Prod) (@Struct_sigma (Functor B C) (λ _ : τ (Functor B C), Functor B C) X X))) (@comp_fapp0
  (Functor_cat B C) W (@fapp0 (Functor_cat B (Product_cat C C)) (Functor_cat B C) (@comp_cat_cov_func B (Product_cat C
  C) C Prod) (@Struct_sigma (Functor B C) (λ _ : τ (Functor B C), Functor B C) W W)) (@fapp0 (Functor_cat B
  (Product_cat C C)) (Functor_cat B C) (@comp_cat_cov_func B (Product_cat C C) C Prod) (@Struct_sigma (Functor B C) (λ
  _ : τ (Functor B C), Functor B C) X X)) (@product_family_map B C Prod W W X X h h)
  (@one_cat_product_family_pair B C C1 Prod BP W W W (@id (Functor_cat B C) W) (@id (Functor_cat B C) W)))
  (@one_cat_product_family_pair B C C1 Prod BP W X X h h) (@one_cat_product_pair_target_path B C C1 Prod BP W W
  W X X (@id (Functor_cat B C) W) (@id (Functor_cat B C) W) h h)));

// (f+g)∘h=(f∘h)+(g∘h) via whole mate naturality and original diagonal pairing.
symbol one_cat_additive_family_precompose_path [B C : Cat] (C1 : τ (IsNCat (cat_succ cat_zero) C)) [Prod : τ
  (Functor (Product_cat C C) C)] [t : τ (Obj C)] (A : τ (@AdditiveCategory C Prod t)) (T0 : τ (@TerminalObject (Op_cat
  C) t)) (W X Y : τ (Functor B C))
  (f g : τ (@Transf B C X Y)) (h : τ (@Transf B C W X))
  : τ (@= (@Transf B C W Y) (@comp_fapp0 (Functor_cat B C) W X Y (@one_cat_additive_family_add B C C1 Prod t A T0 X Y
  f g) h) (@one_cat_additive_family_add B C C1 Prod t A T0 W Y (@comp_fapp0 (Functor_cat B C) W X Y f h) (@comp_fapp0
  (Functor_cat B C) W X Y g h)))
≔ (@eq_trans (@Transf B C W Y) (@comp_fapp0 (Functor_cat B C) W X Y (@one_cat_additive_family_add B C C1 Prod t A T0 X
  Y f g) h) (@comp_fapp0 (Functor_cat B C) W X Y (@comp_fapp0 (Functor_cat B C) X (@fapp0 (Functor_cat B (Product_cat
  C C)) (Functor_cat B C) (@comp_cat_cov_func B (Product_cat C C) C Prod) (@Struct_sigma (Functor B C) (λ _ : τ
  (Functor B C), Functor B C) X X)) Y (@one_cat_copair_family B C C1 Prod t A T0 X X Y f g)
  (@one_cat_product_family_pair B C C1 Prod (@additive_binary_products C Prod t A) X X X (@id (Functor_cat B C) X)
  (@id (Functor_cat B C) X))) h) (@one_cat_additive_family_add B C C1 Prod t A T0 W Y (@comp_fapp0 (Functor_cat B C) W
  X Y f h) (@comp_fapp0 (Functor_cat B C) W X Y g h)) (@eq_ap (@Transf B C X Y) (@Transf B C W Y) (λ k : τ (@Transf B
  C X Y), (@comp_fapp0 (Functor_cat B C) W X Y k h)) (@one_cat_additive_family_add B C C1 Prod t A T0 X Y f g)
  (@comp_fapp0 (Functor_cat B C) X (@fapp0 (Functor_cat B (Product_cat C C)) (Functor_cat B C) (@comp_cat_cov_func B
  (Product_cat C C) C Prod) (@Struct_sigma (Functor B C) (λ _ : τ (Functor B C), Functor B C) X X)) Y
  (@one_cat_copair_family B C C1 Prod t A T0 X X Y f g) (@one_cat_product_family_pair B C C1 Prod
  (@additive_binary_products C Prod t A) X X X (@id (Functor_cat B C) X) (@id (Functor_cat B C) X)))
  (@one_cat_additive_family_add_formula_path B C C1 Prod t A T0 X Y f g)) (@eq_trans (@Transf B C W Y) (@comp_fapp0
  (Functor_cat B C) W X Y (@comp_fapp0 (Functor_cat B C) X (@fapp0 (Functor_cat B (Product_cat C C)) (Functor_cat B C)
  (@comp_cat_cov_func B (Product_cat C C) C Prod) (@Struct_sigma (Functor B C) (λ _ : τ (Functor B C), Functor B C) X
  X)) Y (@one_cat_copair_family B C C1 Prod t A T0 X X Y f g) (@one_cat_product_family_pair B C C1 Prod
  (@additive_binary_products C Prod t A) X X X (@id (Functor_cat B C) X) (@id (Functor_cat B C) X))) h) (@comp_fapp0
  (Functor_cat B C) W (@fapp0 (Functor_cat B (Product_cat C C)) (Functor_cat B C) (@comp_cat_cov_func B (Product_cat C
  C) C Prod) (@Struct_sigma (Functor B C) (λ _ : τ (Functor B C), Functor B C) X X)) Y (@one_cat_copair_family B C C1
  Prod t A T0 X X Y f g) (@comp_fapp0 (Functor_cat B C) W X (@fapp0 (Functor_cat B (Product_cat C C)) (Functor_cat B
  C) (@comp_cat_cov_func B (Product_cat C C) C Prod) (@Struct_sigma (Functor B C) (λ _ : τ (Functor B C), Functor B C)
  X X)) (@one_cat_product_family_pair B C C1 Prod (@additive_binary_products C Prod t A) X X X (@id (Functor_cat B C)
  X) (@id (Functor_cat B C) X)) h)) (@one_cat_additive_family_add B C C1 Prod t A T0 W Y (@comp_fapp0 (Functor_cat B
  C) W X Y f h) (@comp_fapp0 (Functor_cat B C) W X Y g h)) (@eq_sym (@Transf B C W Y) (@comp_fapp0 (Functor_cat B C) W
  (@fapp0 (Functor_cat B (Product_cat C C)) (Functor_cat B C) (@comp_cat_cov_func B (Product_cat C C) C Prod)
  (@Struct_sigma (Functor B C) (λ _ : τ (Functor B C), Functor B C) X X)) Y (@one_cat_copair_family B C C1 Prod t A T0
  X X Y f g) (@comp_fapp0 (Functor_cat B C) W X (@fapp0 (Functor_cat B (Product_cat C C)) (Functor_cat B C)
  (@comp_cat_cov_func B (Product_cat C C) C Prod) (@Struct_sigma (Functor B C) (λ _ : τ (Functor B C), Functor B C) X
  X)) (@one_cat_product_family_pair B C C1 Prod (@additive_binary_products C Prod t A) X X X (@id (Functor_cat B C) X)
  (@id (Functor_cat B C) X)) h)) (@comp_fapp0 (Functor_cat B C) W X Y (@comp_fapp0 (Functor_cat B C) X (@fapp0
  (Functor_cat B (Product_cat C C)) (Functor_cat B C) (@comp_cat_cov_func B (Product_cat C C) C Prod) (@Struct_sigma
  (Functor B C) (λ _ : τ (Functor B C), Functor B C) X X)) Y (@one_cat_copair_family B C C1 Prod t A T0 X X Y f g)
  (@one_cat_product_family_pair B C C1 Prod (@additive_binary_products C Prod t A) X X X (@id (Functor_cat B C) X)
  (@id (Functor_cat B C) X))) h) (@comp_assoc (Functor_cat B C) W X (@fapp0 (Functor_cat B (Product_cat C C))
  (Functor_cat B C) (@comp_cat_cov_func B (Product_cat C C) C Prod) (@Struct_sigma (Functor B C) (λ _ : τ (Functor B
  C), Functor B C) X X)) Y (@one_cat_copair_family B C C1 Prod t A T0 X X Y f g) (@one_cat_product_family_pair B C C1
  Prod (@additive_binary_products C Prod t A) X X X (@id (Functor_cat B C) X) (@id (Functor_cat B C) X)) h))
  (@eq_trans (@Transf B C W Y) (@comp_fapp0 (Functor_cat B C) W (@fapp0 (Functor_cat B (Product_cat C C)) (Functor_cat
  B C) (@comp_cat_cov_func B (Product_cat C C) C Prod) (@Struct_sigma (Functor B C) (λ _ : τ (Functor B C), Functor B
  C) X X)) Y (@one_cat_copair_family B C C1 Prod t A T0 X X Y f g) (@comp_fapp0 (Functor_cat B C) W X (@fapp0
  (Functor_cat B (Product_cat C C)) (Functor_cat B C) (@comp_cat_cov_func B (Product_cat C C) C Prod) (@Struct_sigma
  (Functor B C) (λ _ : τ (Functor B C), Functor B C) X X)) (@one_cat_product_family_pair B C C1 Prod
  (@additive_binary_products C Prod t A) X X X (@id (Functor_cat B C) X) (@id (Functor_cat B C) X)) h)) (@comp_fapp0
  (Functor_cat B C) W (@fapp0 (Functor_cat B (Product_cat C C)) (Functor_cat B C) (@comp_cat_cov_func B (Product_cat C
  C) C Prod) (@Struct_sigma (Functor B C) (λ _ : τ (Functor B C), Functor B C) X X)) Y (@one_cat_copair_family B C C1
  Prod t A T0 X X Y f g) (@comp_fapp0 (Functor_cat B C) W (@fapp0 (Functor_cat B (Product_cat C C)) (Functor_cat B C)
  (@comp_cat_cov_func B (Product_cat C C) C Prod) (@Struct_sigma (Functor B C) (λ _ : τ (Functor B C), Functor B C) W
  W)) (@fapp0 (Functor_cat B (Product_cat C C)) (Functor_cat B C) (@comp_cat_cov_func B (Product_cat C C) C Prod)
  (@Struct_sigma (Functor B C) (λ _ : τ (Functor B C), Functor B C) X X)) (@product_family_map B C Prod W W X X
  h h) (@one_cat_product_family_pair B C C1 Prod (@additive_binary_products C Prod t A) W W W (@id (Functor_cat B C)
  W) (@id (Functor_cat B C) W)))) (@one_cat_additive_family_add B C C1 Prod t A T0 W Y (@comp_fapp0 (Functor_cat B C)
  W X Y f h) (@comp_fapp0 (Functor_cat B C) W X Y g h)) (@eq_ap (@Transf B C W (@fapp0 (Functor_cat B (Product_cat C
  C)) (Functor_cat B C) (@comp_cat_cov_func B (Product_cat C C) C Prod) (@Struct_sigma (Functor B C) (λ _ : τ (Functor
  B C), Functor B C) X X))) (@Transf B C W Y) (λ k : τ (@Transf B C W (@fapp0 (Functor_cat B (Product_cat C C))
  (Functor_cat B C) (@comp_cat_cov_func B (Product_cat C C) C Prod) (@Struct_sigma (Functor B C) (λ _ : τ (Functor B
  C), Functor B C) X X))), (@comp_fapp0 (Functor_cat B C) W (@fapp0 (Functor_cat B (Product_cat C C)) (Functor_cat B
  C) (@comp_cat_cov_func B (Product_cat C C) C Prod) (@Struct_sigma (Functor B C) (λ _ : τ (Functor B C), Functor B C)
  X X)) Y (@one_cat_copair_family B C C1 Prod t A T0 X X Y f g) k)) (@comp_fapp0 (Functor_cat B C) W X (@fapp0
  (Functor_cat B (Product_cat C C)) (Functor_cat B C) (@comp_cat_cov_func B (Product_cat C C) C Prod) (@Struct_sigma
  (Functor B C) (λ _ : τ (Functor B C), Functor B C) X X)) (@one_cat_product_family_pair B C C1 Prod
  (@additive_binary_products C Prod t A) X X X (@id (Functor_cat B C) X) (@id (Functor_cat B C) X)) h) (@comp_fapp0
  (Functor_cat B C) W (@fapp0 (Functor_cat B (Product_cat C C)) (Functor_cat B C) (@comp_cat_cov_func B (Product_cat C
  C) C Prod) (@Struct_sigma (Functor B C) (λ _ : τ (Functor B C), Functor B C) W W)) (@fapp0 (Functor_cat B
  (Product_cat C C)) (Functor_cat B C) (@comp_cat_cov_func B (Product_cat C C) C Prod) (@Struct_sigma (Functor B C) (λ
  _ : τ (Functor B C), Functor B C) X X)) (@product_family_map B C Prod W W X X h h)
  (@one_cat_product_family_pair B C C1 Prod (@additive_binary_products C Prod t A) W W W (@id (Functor_cat B C) W)
  (@id (Functor_cat B C) W))) (@one_cat_product_diagonal_naturality_path B C C1 Prod (@additive_binary_products
  C Prod t A) W X h)) (@eq_trans (@Transf B C W Y) (@comp_fapp0 (Functor_cat B C) W (@fapp0 (Functor_cat B
  (Product_cat C C)) (Functor_cat B C) (@comp_cat_cov_func B (Product_cat C C) C Prod) (@Struct_sigma (Functor B C) (λ
  _ : τ (Functor B C), Functor B C) X X)) Y (@one_cat_copair_family B C C1 Prod t A T0 X X Y f g) (@comp_fapp0
  (Functor_cat B C) W (@fapp0 (Functor_cat B (Product_cat C C)) (Functor_cat B C) (@comp_cat_cov_func B (Product_cat C
  C) C Prod) (@Struct_sigma (Functor B C) (λ _ : τ (Functor B C), Functor B C) W W)) (@fapp0 (Functor_cat B
  (Product_cat C C)) (Functor_cat B C) (@comp_cat_cov_func B (Product_cat C C) C Prod) (@Struct_sigma (Functor B C) (λ
  _ : τ (Functor B C), Functor B C) X X)) (@product_family_map B C Prod W W X X h h)
  (@one_cat_product_family_pair B C C1 Prod (@additive_binary_products C Prod t A) W W W (@id (Functor_cat B C) W)
  (@id (Functor_cat B C) W)))) (@comp_fapp0 (Functor_cat B C) W (@fapp0 (Functor_cat B (Product_cat C C)) (Functor_cat
  B C) (@comp_cat_cov_func B (Product_cat C C) C Prod) (@Struct_sigma (Functor B C) (λ _ : τ (Functor B C), Functor B
  C) W W)) Y (@comp_fapp0 (Functor_cat B C) (@fapp0 (Functor_cat B (Product_cat C C)) (Functor_cat B C)
  (@comp_cat_cov_func B (Product_cat C C) C Prod) (@Struct_sigma (Functor B C) (λ _ : τ (Functor B C), Functor B C) W
  W)) (@fapp0 (Functor_cat B (Product_cat C C)) (Functor_cat B C) (@comp_cat_cov_func B (Product_cat C C) C Prod)
  (@Struct_sigma (Functor B C) (λ _ : τ (Functor B C), Functor B C) X X)) Y (@one_cat_copair_family B C C1 Prod t A T0
  X X Y f g) (@product_family_map B C Prod W W X X h h)) (@one_cat_product_family_pair B C C1 Prod
  (@additive_binary_products C Prod t A) W W W (@id (Functor_cat B C) W) (@id (Functor_cat B C) W)))
  (@one_cat_additive_family_add B C C1 Prod t A T0 W Y (@comp_fapp0 (Functor_cat B C) W X Y f h) (@comp_fapp0
  (Functor_cat B C) W X Y g h)) (@comp_assoc (Functor_cat B C) W (@fapp0 (Functor_cat B (Product_cat C C))
  (Functor_cat B C) (@comp_cat_cov_func B (Product_cat C C) C Prod) (@Struct_sigma (Functor B C) (λ _ : τ (Functor B
  C), Functor B C) W W)) (@fapp0 (Functor_cat B (Product_cat C C)) (Functor_cat B C) (@comp_cat_cov_func B
  (Product_cat C C) C Prod) (@Struct_sigma (Functor B C) (λ _ : τ (Functor B C), Functor B C) X X)) Y
  (@one_cat_copair_family B C C1 Prod t A T0 X X Y f g) (@product_family_map B C Prod W W X X h h)
  (@one_cat_product_family_pair B C C1 Prod (@additive_binary_products C Prod t A) W W W (@id (Functor_cat B C) W)
  (@id (Functor_cat B C) W))) (@eq_trans (@Transf B C W Y) (@comp_fapp0 (Functor_cat B C) W (@fapp0 (Functor_cat B
  (Product_cat C C)) (Functor_cat B C) (@comp_cat_cov_func B (Product_cat C C) C Prod) (@Struct_sigma (Functor B C) (λ
  _ : τ (Functor B C), Functor B C) W W)) Y (@comp_fapp0 (Functor_cat B C) (@fapp0 (Functor_cat B (Product_cat C C))
  (Functor_cat B C) (@comp_cat_cov_func B (Product_cat C C) C Prod) (@Struct_sigma (Functor B C) (λ _ : τ (Functor B
  C), Functor B C) W W)) (@fapp0 (Functor_cat B (Product_cat C C)) (Functor_cat B C) (@comp_cat_cov_func B
  (Product_cat C C) C Prod) (@Struct_sigma (Functor B C) (λ _ : τ (Functor B C), Functor B C) X X)) Y
  (@one_cat_copair_family B C C1 Prod t A T0 X X Y f g) (@product_family_map B C Prod W W X X h h))
  (@one_cat_product_family_pair B C C1 Prod (@additive_binary_products C Prod t A) W W W (@id (Functor_cat B C) W)
  (@id (Functor_cat B C) W))) (@comp_fapp0 (Functor_cat B C) W (@fapp0 (Functor_cat B (Product_cat C C)) (Functor_cat
  B C) (@comp_cat_cov_func B (Product_cat C C) C Prod) (@Struct_sigma (Functor B C) (λ _ : τ (Functor B C), Functor B
  C) W W)) Y (@one_cat_copair_family B C C1 Prod t A T0 W W Y (@comp_fapp0 (Functor_cat B C) W X Y f h) (@comp_fapp0
  (Functor_cat B C) W X Y g h)) (@one_cat_product_family_pair B C C1 Prod (@additive_binary_products C Prod t A) W W W
  (@id (Functor_cat B C) W) (@id (Functor_cat B C) W))) (@one_cat_additive_family_add B C C1 Prod t A T0 W Y
  (@comp_fapp0 (Functor_cat B C) W X Y f h) (@comp_fapp0 (Functor_cat B C) W X Y g h)) (@eq_ap (@Transf B C (@fapp0
  (Functor_cat B (Product_cat C C)) (Functor_cat B C) (@comp_cat_cov_func B (Product_cat C C) C Prod) (@Struct_sigma
  (Functor B C) (λ _ : τ (Functor B C), Functor B C) W W)) Y) (@Transf B C W Y) (λ k : τ (@Transf B C (@fapp0
  (Functor_cat B (Product_cat C C)) (Functor_cat B C) (@comp_cat_cov_func B (Product_cat C C) C Prod) (@Struct_sigma
  (Functor B C) (λ _ : τ (Functor B C), Functor B C) W W)) Y), (@comp_fapp0 (Functor_cat B C) W (@fapp0 (Functor_cat B
  (Product_cat C C)) (Functor_cat B C) (@comp_cat_cov_func B (Product_cat C C) C Prod) (@Struct_sigma (Functor B C) (λ
  _ : τ (Functor B C), Functor B C) W W)) Y k (@one_cat_product_family_pair B C C1 Prod (@additive_binary_products C
  Prod t A) W W W (@id (Functor_cat B C) W) (@id (Functor_cat B C) W)))) (@comp_fapp0 (Functor_cat B C) (@fapp0
  (Functor_cat B (Product_cat C C)) (Functor_cat B C) (@comp_cat_cov_func B (Product_cat C C) C Prod) (@Struct_sigma
  (Functor B C) (λ _ : τ (Functor B C), Functor B C) W W)) (@fapp0 (Functor_cat B (Product_cat C C)) (Functor_cat B C)
  (@comp_cat_cov_func B (Product_cat C C) C Prod) (@Struct_sigma (Functor B C) (λ _ : τ (Functor B C), Functor B C) X
  X)) Y (@one_cat_copair_family B C C1 Prod t A T0 X X Y f g) (@product_family_map B C Prod W W X X h h))
  (@one_cat_copair_family B C C1 Prod t A T0 W W Y (@comp_fapp0 (Functor_cat B C) W X Y f h) (@comp_fapp0 (Functor_cat
  B C) W X Y g h)) (@one_cat_copair_source_path B C C1 Prod t A T0 W W X X Y h h f g)) (@eq_sym (@Transf B C W
  Y) (@one_cat_additive_family_add B C C1 Prod t A T0 W Y (@comp_fapp0 (Functor_cat B C) W X Y f h) (@comp_fapp0
  (Functor_cat B C) W X Y g h)) (@comp_fapp0 (Functor_cat B C) W (@fapp0 (Functor_cat B (Product_cat C C))
  (Functor_cat B C) (@comp_cat_cov_func B (Product_cat C C) C Prod) (@Struct_sigma (Functor B C) (λ _ : τ (Functor B
  C), Functor B C) W W)) Y (@one_cat_copair_family B C C1 Prod t A T0 W W Y (@comp_fapp0 (Functor_cat B C) W X Y f h)
  (@comp_fapp0 (Functor_cat B C) W X Y g h)) (@one_cat_product_family_pair B C C1 Prod (@additive_binary_products C
  Prod t A) W W W (@id (Functor_cat B C) W) (@id (Functor_cat B C) W))) (@one_cat_additive_family_add_formula_path B C
  C1 Prod t A T0 W Y (@comp_fapp0 (Functor_cat B C) W X Y f h) (@comp_fapp0 (Functor_cat B C) W X Y g h))))))));
