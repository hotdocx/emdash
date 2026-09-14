require open emdash.emdash3_2_one_cat_additive_family_cancellation;
require open emdash.emdash3_2_one_cat_product_family_projection_paths;
require open emdash.emdash3_2_one_cat_zero_family_postcomposition_paths;

// The original whole difference of the two projected cospan legs.
symbol one_cat_difference_cospan_transf [B C : Cat] (C1 : τ (IsNCat (cat_succ cat_zero) C)) [Prod : τ
  (Functor (Product_cat C C) C)] [t : τ (Obj C)] (A : τ (@AdditiveCategory C Prod t)) (T0 : τ (@TerminalObject
  (Op_cat C) t)) (X Y Z : τ (Functor B C)) (f : τ (@Transf B C X Z)) (g : τ (@Transf B C Y Z))
  : τ (@Transf B C (@fapp0 (Functor_cat B (Product_cat C C)) (Functor_cat B C) (@comp_cat_cov_func B (Product_cat
  C C) C Prod) (@Struct_sigma (Functor B C) (λ _ : τ (Functor B C), Functor B C) X Y)) Z) ≔
  (@one_cat_difference_family B C C1 Prod t A T0 (@fapp0 (Functor_cat B (Product_cat C C)) (Functor_cat B C)
  (@comp_cat_cov_func B (Product_cat C C) C Prod) (@Struct_sigma (Functor B C) (λ _ : τ (Functor B C), Functor B
  C) X Y)) Z (@comp_fapp0 (Functor_cat B C) (@fapp0 (Functor_cat B (Product_cat C C)) (Functor_cat B C)
  (@comp_cat_cov_func B (Product_cat C C) C Prod) (@Struct_sigma (Functor B C) (λ _ : τ (Functor B C), Functor B
  C) X Y)) X Z f (@one_cat_product_family_proj1 B C C1 Prod (@additive_binary_products C Prod t A) X Y))
  (@comp_fapp0 (Functor_cat B C) (@fapp0 (Functor_cat B (Product_cat C C)) (Functor_cat B C) (@comp_cat_cov_func B
  (Product_cat C C) C Prod) (@Struct_sigma (Functor B C) (λ _ : τ (Functor B C), Functor B C) X Y)) Y Z g
  (@one_cat_product_family_proj2 B C C1 Prod (@additive_binary_products C Prod t A) X Y)));

// The original whole pairing evaluates both cospan legs.
symbol one_cat_difference_cospan_pair_path [B C : Cat] (C1 : τ (IsNCat (cat_succ cat_zero) C)) [Prod : τ
  (Functor (Product_cat C C) C)] [t : τ (Obj C)] (A : τ (@AdditiveCategory C Prod t)) (T0 : τ (@TerminalObject
  (Op_cat C) t)) (X Y Z : τ (Functor B C)) (f : τ (@Transf B C X Z)) (g : τ (@Transf B C Y Z)) (I : τ (Functor B
  C)) (a : τ (@Transf B C I X)) (b : τ (@Transf B C I Y))
  : τ (@= (@Transf B C I Z) (@comp_fapp0 (Functor_cat B C) I (@fapp0 (Functor_cat B (Product_cat C C))
  (Functor_cat B C) (@comp_cat_cov_func B (Product_cat C C) C Prod) (@Struct_sigma (Functor B C) (λ _ : τ (Functor
  B C), Functor B C) X Y)) Z (@one_cat_difference_cospan_transf B C C1 Prod t A T0 X Y Z f g)
  (@one_cat_product_family_pair B C C1 Prod (@additive_binary_products C Prod t A) I X Y a b))
  (@one_cat_difference_family B C C1 Prod t A T0 I Z (@comp_fapp0 (Functor_cat B C) I X Z f a) (@comp_fapp0
  (Functor_cat B C) I Y Z g b)))
≔ (@eq_trans (@Transf B C I Z) (@comp_fapp0 (Functor_cat B C) I (@fapp0 (Functor_cat B (Product_cat C C))
  (Functor_cat B C) (@comp_cat_cov_func B (Product_cat C C) C Prod) (@Struct_sigma (Functor B C) (λ _ : τ (Functor
  B C), Functor B C) X Y)) Z (@one_cat_difference_cospan_transf B C C1 Prod t A T0 X Y Z f g)
  (@one_cat_product_family_pair B C C1 Prod (@additive_binary_products C Prod t A) I X Y a b))
  (@one_cat_difference_family B C C1 Prod t A T0 I Z (@comp_fapp0 (Functor_cat B C) I (@fapp0 (Functor_cat B
  (Product_cat C C)) (Functor_cat B C) (@comp_cat_cov_func B (Product_cat C C) C Prod) (@Struct_sigma (Functor B
  C) (λ _ : τ (Functor B C), Functor B C) X Y)) Z (@comp_fapp0 (Functor_cat B C) (@fapp0 (Functor_cat B
  (Product_cat C C)) (Functor_cat B C) (@comp_cat_cov_func B (Product_cat C C) C Prod) (@Struct_sigma (Functor B
  C) (λ _ : τ (Functor B C), Functor B C) X Y)) X Z f (@one_cat_product_family_proj1 B C C1 Prod
  (@additive_binary_products C Prod t A) X Y)) (@one_cat_product_family_pair B C C1 Prod
  (@additive_binary_products C Prod t A) I X Y a b)) (@comp_fapp0 (Functor_cat B C) I (@fapp0 (Functor_cat B
  (Product_cat C C)) (Functor_cat B C) (@comp_cat_cov_func B (Product_cat C C) C Prod) (@Struct_sigma (Functor B
  C) (λ _ : τ (Functor B C), Functor B C) X Y)) Z (@comp_fapp0 (Functor_cat B C) (@fapp0 (Functor_cat B
  (Product_cat C C)) (Functor_cat B C) (@comp_cat_cov_func B (Product_cat C C) C Prod) (@Struct_sigma (Functor B
  C) (λ _ : τ (Functor B C), Functor B C) X Y)) Y Z g (@one_cat_product_family_proj2 B C C1 Prod
  (@additive_binary_products C Prod t A) X Y)) (@one_cat_product_family_pair B C C1 Prod
  (@additive_binary_products C Prod t A) I X Y a b))) (@one_cat_difference_family B C C1 Prod t A T0 I Z
  (@comp_fapp0 (Functor_cat B C) I X Z f a) (@comp_fapp0 (Functor_cat B C) I Y Z g b))
  (@one_cat_difference_family_precompose_path B C C1 Prod t A T0 I (@fapp0 (Functor_cat B (Product_cat C C))
  (Functor_cat B C) (@comp_cat_cov_func B (Product_cat C C) C Prod) (@Struct_sigma (Functor B C) (λ _ : τ (Functor
  B C), Functor B C) X Y)) Z (@comp_fapp0 (Functor_cat B C) (@fapp0 (Functor_cat B (Product_cat C C)) (Functor_cat
  B C) (@comp_cat_cov_func B (Product_cat C C) C Prod) (@Struct_sigma (Functor B C) (λ _ : τ (Functor B C),
  Functor B C) X Y)) X Z f (@one_cat_product_family_proj1 B C C1 Prod (@additive_binary_products C Prod t A) X Y))
  (@comp_fapp0 (Functor_cat B C) (@fapp0 (Functor_cat B (Product_cat C C)) (Functor_cat B C) (@comp_cat_cov_func B
  (Product_cat C C) C Prod) (@Struct_sigma (Functor B C) (λ _ : τ (Functor B C), Functor B C) X Y)) Y Z g
  (@one_cat_product_family_proj2 B C C1 Prod (@additive_binary_products C Prod t A) X Y))
  (@one_cat_product_family_pair B C C1 Prod (@additive_binary_products C Prod t A) I X Y a b)) (@eq_trans (@Transf
  B C I Z) (@one_cat_difference_family B C C1 Prod t A T0 I Z (@comp_fapp0 (Functor_cat B C) I (@fapp0
  (Functor_cat B (Product_cat C C)) (Functor_cat B C) (@comp_cat_cov_func B (Product_cat C C) C Prod)
  (@Struct_sigma (Functor B C) (λ _ : τ (Functor B C), Functor B C) X Y)) Z (@comp_fapp0 (Functor_cat B C) (@fapp0
  (Functor_cat B (Product_cat C C)) (Functor_cat B C) (@comp_cat_cov_func B (Product_cat C C) C Prod)
  (@Struct_sigma (Functor B C) (λ _ : τ (Functor B C), Functor B C) X Y)) X Z f (@one_cat_product_family_proj1 B C
  C1 Prod (@additive_binary_products C Prod t A) X Y)) (@one_cat_product_family_pair B C C1 Prod
  (@additive_binary_products C Prod t A) I X Y a b)) (@comp_fapp0 (Functor_cat B C) I (@fapp0 (Functor_cat B
  (Product_cat C C)) (Functor_cat B C) (@comp_cat_cov_func B (Product_cat C C) C Prod) (@Struct_sigma (Functor B
  C) (λ _ : τ (Functor B C), Functor B C) X Y)) Z (@comp_fapp0 (Functor_cat B C) (@fapp0 (Functor_cat B
  (Product_cat C C)) (Functor_cat B C) (@comp_cat_cov_func B (Product_cat C C) C Prod) (@Struct_sigma (Functor B
  C) (λ _ : τ (Functor B C), Functor B C) X Y)) Y Z g (@one_cat_product_family_proj2 B C C1 Prod
  (@additive_binary_products C Prod t A) X Y)) (@one_cat_product_family_pair B C C1 Prod
  (@additive_binary_products C Prod t A) I X Y a b))) (@one_cat_difference_family B C C1 Prod t A T0 I Z
  (@comp_fapp0 (Functor_cat B C) I X Z f a) (@comp_fapp0 (Functor_cat B C) I (@fapp0 (Functor_cat B (Product_cat C
  C)) (Functor_cat B C) (@comp_cat_cov_func B (Product_cat C C) C Prod) (@Struct_sigma (Functor B C) (λ _ : τ
  (Functor B C), Functor B C) X Y)) Z (@comp_fapp0 (Functor_cat B C) (@fapp0 (Functor_cat B (Product_cat C C))
  (Functor_cat B C) (@comp_cat_cov_func B (Product_cat C C) C Prod) (@Struct_sigma (Functor B C) (λ _ : τ (Functor
  B C), Functor B C) X Y)) Y Z g (@one_cat_product_family_proj2 B C C1 Prod (@additive_binary_products C Prod t A)
  X Y)) (@one_cat_product_family_pair B C C1 Prod (@additive_binary_products C Prod t A) I X Y a b)))
  (@one_cat_difference_family B C C1 Prod t A T0 I Z (@comp_fapp0 (Functor_cat B C) I X Z f a) (@comp_fapp0
  (Functor_cat B C) I Y Z g b)) (@eq_ap (@Transf B C I Z) (@Transf B C I Z) (λ u : τ (@Transf B C I Z),
  (@one_cat_difference_family B C C1 Prod t A T0 I Z u (@comp_fapp0 (Functor_cat B C) I (@fapp0 (Functor_cat B
  (Product_cat C C)) (Functor_cat B C) (@comp_cat_cov_func B (Product_cat C C) C Prod) (@Struct_sigma (Functor B
  C) (λ _ : τ (Functor B C), Functor B C) X Y)) Z (@comp_fapp0 (Functor_cat B C) (@fapp0 (Functor_cat B
  (Product_cat C C)) (Functor_cat B C) (@comp_cat_cov_func B (Product_cat C C) C Prod) (@Struct_sigma (Functor B
  C) (λ _ : τ (Functor B C), Functor B C) X Y)) Y Z g (@one_cat_product_family_proj2 B C C1 Prod
  (@additive_binary_products C Prod t A) X Y)) (@one_cat_product_family_pair B C C1 Prod
  (@additive_binary_products C Prod t A) I X Y a b)))) (@comp_fapp0 (Functor_cat B C) I (@fapp0 (Functor_cat B
  (Product_cat C C)) (Functor_cat B C) (@comp_cat_cov_func B (Product_cat C C) C Prod) (@Struct_sigma (Functor B
  C) (λ _ : τ (Functor B C), Functor B C) X Y)) Z (@comp_fapp0 (Functor_cat B C) (@fapp0 (Functor_cat B
  (Product_cat C C)) (Functor_cat B C) (@comp_cat_cov_func B (Product_cat C C) C Prod) (@Struct_sigma (Functor B
  C) (λ _ : τ (Functor B C), Functor B C) X Y)) X Z f (@one_cat_product_family_proj1 B C C1 Prod
  (@additive_binary_products C Prod t A) X Y)) (@one_cat_product_family_pair B C C1 Prod
  (@additive_binary_products C Prod t A) I X Y a b)) (@comp_fapp0 (Functor_cat B C) I X Z f a) (@eq_trans (@Transf
  B C I Z) (@comp_fapp0 (Functor_cat B C) I (@fapp0 (Functor_cat B (Product_cat C C)) (Functor_cat B C)
  (@comp_cat_cov_func B (Product_cat C C) C Prod) (@Struct_sigma (Functor B C) (λ _ : τ (Functor B C), Functor B
  C) X Y)) Z (@comp_fapp0 (Functor_cat B C) (@fapp0 (Functor_cat B (Product_cat C C)) (Functor_cat B C)
  (@comp_cat_cov_func B (Product_cat C C) C Prod) (@Struct_sigma (Functor B C) (λ _ : τ (Functor B C), Functor B
  C) X Y)) X Z f (@one_cat_product_family_proj1 B C C1 Prod (@additive_binary_products C Prod t A) X Y))
  (@one_cat_product_family_pair B C C1 Prod (@additive_binary_products C Prod t A) I X Y a b)) (@comp_fapp0
  (Functor_cat B C) I X Z f (@comp_fapp0 (Functor_cat B C) I (@fapp0 (Functor_cat B (Product_cat C C))
  (Functor_cat B C) (@comp_cat_cov_func B (Product_cat C C) C Prod) (@Struct_sigma (Functor B C) (λ _ : τ (Functor
  B C), Functor B C) X Y)) X (@one_cat_product_family_proj1 B C C1 Prod (@additive_binary_products C Prod t A) X
  Y) (@one_cat_product_family_pair B C C1 Prod (@additive_binary_products C Prod t A) I X Y a b))) (@comp_fapp0
  (Functor_cat B C) I X Z f a) (@eq_sym (@Transf B C I Z) (@comp_fapp0 (Functor_cat B C) I X Z f (@comp_fapp0
  (Functor_cat B C) I (@fapp0 (Functor_cat B (Product_cat C C)) (Functor_cat B C) (@comp_cat_cov_func B
  (Product_cat C C) C Prod) (@Struct_sigma (Functor B C) (λ _ : τ (Functor B C), Functor B C) X Y)) X
  (@one_cat_product_family_proj1 B C C1 Prod (@additive_binary_products C Prod t A) X Y)
  (@one_cat_product_family_pair B C C1 Prod (@additive_binary_products C Prod t A) I X Y a b))) (@comp_fapp0
  (Functor_cat B C) I (@fapp0 (Functor_cat B (Product_cat C C)) (Functor_cat B C) (@comp_cat_cov_func B
  (Product_cat C C) C Prod) (@Struct_sigma (Functor B C) (λ _ : τ (Functor B C), Functor B C) X Y)) Z (@comp_fapp0
  (Functor_cat B C) (@fapp0 (Functor_cat B (Product_cat C C)) (Functor_cat B C) (@comp_cat_cov_func B (Product_cat
  C C) C Prod) (@Struct_sigma (Functor B C) (λ _ : τ (Functor B C), Functor B C) X Y)) X Z f
  (@one_cat_product_family_proj1 B C C1 Prod (@additive_binary_products C Prod t A) X Y))
  (@one_cat_product_family_pair B C C1 Prod (@additive_binary_products C Prod t A) I X Y a b)) (@comp_assoc
  (Functor_cat B C) I (@fapp0 (Functor_cat B (Product_cat C C)) (Functor_cat B C) (@comp_cat_cov_func B
  (Product_cat C C) C Prod) (@Struct_sigma (Functor B C) (λ _ : τ (Functor B C), Functor B C) X Y)) X Z f
  (@one_cat_product_family_proj1 B C C1 Prod (@additive_binary_products C Prod t A) X Y)
  (@one_cat_product_family_pair B C C1 Prod (@additive_binary_products C Prod t A) I X Y a b))) (@eq_ap (@Transf B
  C I X) (@Transf B C I Z) (λ u : τ (@Transf B C I X), (@comp_fapp0 (Functor_cat B C) I X Z f u)) (@comp_fapp0
  (Functor_cat B C) I (@fapp0 (Functor_cat B (Product_cat C C)) (Functor_cat B C) (@comp_cat_cov_func B
  (Product_cat C C) C Prod) (@Struct_sigma (Functor B C) (λ _ : τ (Functor B C), Functor B C) X Y)) X
  (@one_cat_product_family_proj1 B C C1 Prod (@additive_binary_products C Prod t A) X Y)
  (@one_cat_product_family_pair B C C1 Prod (@additive_binary_products C Prod t A) I X Y a b)) a
  (@one_cat_product_family_pair_proj1_path B C C1 Prod (@additive_binary_products C Prod t A) I X Y a b))))
  (@eq_ap (@Transf B C I Z) (@Transf B C I Z) (λ u : τ (@Transf B C I Z), (@one_cat_difference_family B C C1 Prod
  t A T0 I Z (@comp_fapp0 (Functor_cat B C) I X Z f a) u)) (@comp_fapp0 (Functor_cat B C) I (@fapp0 (Functor_cat B
  (Product_cat C C)) (Functor_cat B C) (@comp_cat_cov_func B (Product_cat C C) C Prod) (@Struct_sigma (Functor B
  C) (λ _ : τ (Functor B C), Functor B C) X Y)) Z (@comp_fapp0 (Functor_cat B C) (@fapp0 (Functor_cat B
  (Product_cat C C)) (Functor_cat B C) (@comp_cat_cov_func B (Product_cat C C) C Prod) (@Struct_sigma (Functor B
  C) (λ _ : τ (Functor B C), Functor B C) X Y)) Y Z g (@one_cat_product_family_proj2 B C C1 Prod
  (@additive_binary_products C Prod t A) X Y)) (@one_cat_product_family_pair B C C1 Prod
  (@additive_binary_products C Prod t A) I X Y a b)) (@comp_fapp0 (Functor_cat B C) I Y Z g b) (@eq_trans (@Transf
  B C I Z) (@comp_fapp0 (Functor_cat B C) I (@fapp0 (Functor_cat B (Product_cat C C)) (Functor_cat B C)
  (@comp_cat_cov_func B (Product_cat C C) C Prod) (@Struct_sigma (Functor B C) (λ _ : τ (Functor B C), Functor B
  C) X Y)) Z (@comp_fapp0 (Functor_cat B C) (@fapp0 (Functor_cat B (Product_cat C C)) (Functor_cat B C)
  (@comp_cat_cov_func B (Product_cat C C) C Prod) (@Struct_sigma (Functor B C) (λ _ : τ (Functor B C), Functor B
  C) X Y)) Y Z g (@one_cat_product_family_proj2 B C C1 Prod (@additive_binary_products C Prod t A) X Y))
  (@one_cat_product_family_pair B C C1 Prod (@additive_binary_products C Prod t A) I X Y a b)) (@comp_fapp0
  (Functor_cat B C) I Y Z g (@comp_fapp0 (Functor_cat B C) I (@fapp0 (Functor_cat B (Product_cat C C))
  (Functor_cat B C) (@comp_cat_cov_func B (Product_cat C C) C Prod) (@Struct_sigma (Functor B C) (λ _ : τ (Functor
  B C), Functor B C) X Y)) Y (@one_cat_product_family_proj2 B C C1 Prod (@additive_binary_products C Prod t A) X
  Y) (@one_cat_product_family_pair B C C1 Prod (@additive_binary_products C Prod t A) I X Y a b))) (@comp_fapp0
  (Functor_cat B C) I Y Z g b) (@eq_sym (@Transf B C I Z) (@comp_fapp0 (Functor_cat B C) I Y Z g (@comp_fapp0
  (Functor_cat B C) I (@fapp0 (Functor_cat B (Product_cat C C)) (Functor_cat B C) (@comp_cat_cov_func B
  (Product_cat C C) C Prod) (@Struct_sigma (Functor B C) (λ _ : τ (Functor B C), Functor B C) X Y)) Y
  (@one_cat_product_family_proj2 B C C1 Prod (@additive_binary_products C Prod t A) X Y)
  (@one_cat_product_family_pair B C C1 Prod (@additive_binary_products C Prod t A) I X Y a b))) (@comp_fapp0
  (Functor_cat B C) I (@fapp0 (Functor_cat B (Product_cat C C)) (Functor_cat B C) (@comp_cat_cov_func B
  (Product_cat C C) C Prod) (@Struct_sigma (Functor B C) (λ _ : τ (Functor B C), Functor B C) X Y)) Z (@comp_fapp0
  (Functor_cat B C) (@fapp0 (Functor_cat B (Product_cat C C)) (Functor_cat B C) (@comp_cat_cov_func B (Product_cat
  C C) C Prod) (@Struct_sigma (Functor B C) (λ _ : τ (Functor B C), Functor B C) X Y)) Y Z g
  (@one_cat_product_family_proj2 B C C1 Prod (@additive_binary_products C Prod t A) X Y))
  (@one_cat_product_family_pair B C C1 Prod (@additive_binary_products C Prod t A) I X Y a b)) (@comp_assoc
  (Functor_cat B C) I (@fapp0 (Functor_cat B (Product_cat C C)) (Functor_cat B C) (@comp_cat_cov_func B
  (Product_cat C C) C Prod) (@Struct_sigma (Functor B C) (λ _ : τ (Functor B C), Functor B C) X Y)) Y Z g
  (@one_cat_product_family_proj2 B C C1 Prod (@additive_binary_products C Prod t A) X Y)
  (@one_cat_product_family_pair B C C1 Prod (@additive_binary_products C Prod t A) I X Y a b))) (@eq_ap (@Transf B
  C I Y) (@Transf B C I Z) (λ u : τ (@Transf B C I Y), (@comp_fapp0 (Functor_cat B C) I Y Z g u)) (@comp_fapp0
  (Functor_cat B C) I (@fapp0 (Functor_cat B (Product_cat C C)) (Functor_cat B C) (@comp_cat_cov_func B
  (Product_cat C C) C Prod) (@Struct_sigma (Functor B C) (λ _ : τ (Functor B C), Functor B C) X Y)) Y
  (@one_cat_product_family_proj2 B C C1 Prod (@additive_binary_products C Prod t A) X Y)
  (@one_cat_product_family_pair B C C1 Prod (@additive_binary_products C Prod t A) I X Y a b)) b
  (@one_cat_product_family_pair_proj2_path B C C1 Prod (@additive_binary_products C Prod t A) I X Y a b))))));

// Whole postcomposition preserves that paired difference.
symbol one_cat_difference_cospan_postcompose_pair_path [B C : Cat] (C1 : τ (IsNCat (cat_succ cat_zero) C))
  [Prod : τ (Functor (Product_cat C C) C)] [t : τ (Obj C)] (A : τ (@AdditiveCategory C Prod t)) (T0 : τ
  (@TerminalObject (Op_cat C) t)) (X Y Z : τ (Functor B C)) (f : τ (@Transf B C X Z)) (g : τ (@Transf B C Y Z)) (I
  : τ (Functor B C)) (a : τ (@Transf B C I X)) (b : τ (@Transf B C I Y)) (V : τ (Functor B C)) (h : τ (@Transf B C
  Z V))
  : τ (@= (@Transf B C I V) (@comp_fapp0 (Functor_cat B C) I Z V h (@comp_fapp0 (Functor_cat B C) I (@fapp0
  (Functor_cat B (Product_cat C C)) (Functor_cat B C) (@comp_cat_cov_func B (Product_cat C C) C Prod)
  (@Struct_sigma (Functor B C) (λ _ : τ (Functor B C), Functor B C) X Y)) Z
  (@one_cat_difference_cospan_transf B C C1 Prod t A T0 X Y Z f g) (@one_cat_product_family_pair B C C1 Prod
  (@additive_binary_products C Prod t A) I X Y a b))) (@one_cat_difference_family B C C1 Prod t A T0 I V
  (@comp_fapp0 (Functor_cat B C) I Z V h (@comp_fapp0 (Functor_cat B C) I X Z f a)) (@comp_fapp0 (Functor_cat B C)
  I Z V h (@comp_fapp0 (Functor_cat B C) I Y Z g b))))
≔ (@eq_trans (@Transf B C I V) (@comp_fapp0 (Functor_cat B C) I Z V h (@comp_fapp0 (Functor_cat B C) I (@fapp0
  (Functor_cat B (Product_cat C C)) (Functor_cat B C) (@comp_cat_cov_func B (Product_cat C C) C Prod)
  (@Struct_sigma (Functor B C) (λ _ : τ (Functor B C), Functor B C) X Y)) Z
  (@one_cat_difference_cospan_transf B C C1 Prod t A T0 X Y Z f g) (@one_cat_product_family_pair B C C1 Prod
  (@additive_binary_products C Prod t A) I X Y a b))) (@comp_fapp0 (Functor_cat B C) I Z V h
  (@one_cat_difference_family B C C1 Prod t A T0 I Z (@comp_fapp0 (Functor_cat B C) I X Z f a) (@comp_fapp0
  (Functor_cat B C) I Y Z g b))) (@one_cat_difference_family B C C1 Prod t A T0 I V (@comp_fapp0 (Functor_cat B C)
  I Z V h (@comp_fapp0 (Functor_cat B C) I X Z f a)) (@comp_fapp0 (Functor_cat B C) I Z V h (@comp_fapp0
  (Functor_cat B C) I Y Z g b))) (@eq_ap (@Transf B C I Z) (@Transf B C I V) (λ u : τ (@Transf B C I Z),
  (@comp_fapp0 (Functor_cat B C) I Z V h u)) (@comp_fapp0 (Functor_cat B C) I (@fapp0 (Functor_cat B (Product_cat
  C C)) (Functor_cat B C) (@comp_cat_cov_func B (Product_cat C C) C Prod) (@Struct_sigma (Functor B C) (λ _ : τ
  (Functor B C), Functor B C) X Y)) Z (@one_cat_difference_cospan_transf B C C1 Prod t A T0 X Y Z f g)
  (@one_cat_product_family_pair B C C1 Prod (@additive_binary_products C Prod t A) I X Y a b))
  (@one_cat_difference_family B C C1 Prod t A T0 I Z (@comp_fapp0 (Functor_cat B C) I X Z f a) (@comp_fapp0
  (Functor_cat B C) I Y Z g b)) (@one_cat_difference_cospan_pair_path B C C1 Prod t A T0 X Y Z f g I a b))
  (@one_cat_difference_family_postcompose_path B C C1 Prod t A T0 I Z V (@comp_fapp0 (Functor_cat B C) I X Z f a)
  (@comp_fapp0 (Functor_cat B C) I Y Z g b) h));

// Annihilating the difference forces annihilation of its original second leg.
symbol one_cat_difference_cospan_annihilator_path [B C : Cat] (C1 : τ (IsNCat (cat_succ cat_zero) C)) [Prod
  : τ (Functor (Product_cat C C) C)] [t : τ (Obj C)] (A : τ (@AdditiveCategory C Prod t)) (T0 : τ (@TerminalObject
  (Op_cat C) t)) (X Y Z : τ (Functor B C)) (f : τ (@Transf B C X Z)) (g : τ (@Transf B C Y Z)) (V : τ (Functor B
  C)) (h : τ (@Transf B C Z V)) (z : τ (@= (@Transf B C (@fapp0 (Functor_cat B (Product_cat C C)) (Functor_cat B
  C) (@comp_cat_cov_func B (Product_cat C C) C Prod) (@Struct_sigma (Functor B C) (λ _ : τ (Functor B C), Functor
  B C) X Y)) V) (@comp_fapp0 (Functor_cat B C) (@fapp0 (Functor_cat B (Product_cat C C)) (Functor_cat B C)
  (@comp_cat_cov_func B (Product_cat C C) C Prod) (@Struct_sigma (Functor B C) (λ _ : τ (Functor B C), Functor B
  C) X Y)) Z V h (@one_cat_difference_cospan_transf B C C1 Prod t A T0 X Y Z f g))
  (@zero_arrow_family_zero_transf B C t (@additive_terminal_object C Prod t A) T0 (@fapp0 (Functor_cat B
  (Product_cat C C)) (Functor_cat B C) (@comp_cat_cov_func B (Product_cat C C) C Prod) (@Struct_sigma (Functor B
  C) (λ _ : τ (Functor B C), Functor B C) X Y)) V)))
  : τ (@= (@Transf B C Y V) (@comp_fapp0 (Functor_cat B C) Y Z V h g) (@zero_arrow_family_zero_transf B C t
  (@additive_terminal_object C Prod t A) T0 Y V))
≔ (@eq_trans (@Transf B C Y V) (@comp_fapp0 (Functor_cat B C) Y Z V h g) (@comp_fapp0 (Functor_cat B C) Y Z V h
  (@comp_fapp0 (Functor_cat B C) Y X Z f (@zero_arrow_family_zero_transf B C t (@additive_terminal_object C Prod t
  A) T0 Y X))) (@zero_arrow_family_zero_transf B C t (@additive_terminal_object C Prod t A) T0 Y V) (@eq_sym
  (@Transf B C Y V) (@comp_fapp0 (Functor_cat B C) Y Z V h (@comp_fapp0 (Functor_cat B C) Y X Z f
  (@zero_arrow_family_zero_transf B C t (@additive_terminal_object C Prod t A) T0 Y X))) (@comp_fapp0 (Functor_cat
  B C) Y Z V h g) (@one_cat_difference_family_zero_reflect B C C1 Prod t A T0 Y V (@comp_fapp0 (Functor_cat B C) Y
  Z V h (@comp_fapp0 (Functor_cat B C) Y X Z f (@zero_arrow_family_zero_transf B C t (@additive_terminal_object C
  Prod t A) T0 Y X))) (@comp_fapp0 (Functor_cat B C) Y Z V h g) (@eq_trans (@Transf B C Y V)
  (@one_cat_difference_family B C C1 Prod t A T0 Y V (@comp_fapp0 (Functor_cat B C) Y Z V h (@comp_fapp0
  (Functor_cat B C) Y X Z f (@zero_arrow_family_zero_transf B C t (@additive_terminal_object C Prod t A) T0 Y X)))
  (@comp_fapp0 (Functor_cat B C) Y Z V h g)) (@comp_fapp0 (Functor_cat B C) Y Z V h (@comp_fapp0 (Functor_cat B C)
  Y (@fapp0 (Functor_cat B (Product_cat C C)) (Functor_cat B C) (@comp_cat_cov_func B (Product_cat C C) C Prod)
  (@Struct_sigma (Functor B C) (λ _ : τ (Functor B C), Functor B C) X Y)) Z
  (@one_cat_difference_cospan_transf B C C1 Prod t A T0 X Y Z f g) (@one_cat_product_family_pair B C C1 Prod
  (@additive_binary_products C Prod t A) Y X Y (@zero_arrow_family_zero_transf B C t (@additive_terminal_object C
  Prod t A) T0 Y X) (@id (Functor_cat B C) Y)))) (@zero_arrow_family_zero_transf B C t (@additive_terminal_object
  C Prod t A) T0 Y V) (@eq_sym (@Transf B C Y V) (@comp_fapp0 (Functor_cat B C) Y Z V h (@comp_fapp0 (Functor_cat
  B C) Y (@fapp0 (Functor_cat B (Product_cat C C)) (Functor_cat B C) (@comp_cat_cov_func B (Product_cat C C) C
  Prod) (@Struct_sigma (Functor B C) (λ _ : τ (Functor B C), Functor B C) X Y)) Z
  (@one_cat_difference_cospan_transf B C C1 Prod t A T0 X Y Z f g) (@one_cat_product_family_pair B C C1 Prod
  (@additive_binary_products C Prod t A) Y X Y (@zero_arrow_family_zero_transf B C t (@additive_terminal_object C
  Prod t A) T0 Y X) (@id (Functor_cat B C) Y)))) (@one_cat_difference_family B C C1 Prod t A T0 Y V (@comp_fapp0
  (Functor_cat B C) Y Z V h (@comp_fapp0 (Functor_cat B C) Y X Z f (@zero_arrow_family_zero_transf B C t
  (@additive_terminal_object C Prod t A) T0 Y X))) (@comp_fapp0 (Functor_cat B C) Y Z V h g))
  (@one_cat_difference_cospan_postcompose_pair_path B C C1 Prod t A T0 X Y Z f g Y
  (@zero_arrow_family_zero_transf B C t (@additive_terminal_object C Prod t A) T0 Y X) (@id (Functor_cat B C) Y) V
  h)) (@eq_trans (@Transf B C Y V) (@comp_fapp0 (Functor_cat B C) Y Z V h (@comp_fapp0 (Functor_cat B C) Y (@fapp0
  (Functor_cat B (Product_cat C C)) (Functor_cat B C) (@comp_cat_cov_func B (Product_cat C C) C Prod)
  (@Struct_sigma (Functor B C) (λ _ : τ (Functor B C), Functor B C) X Y)) Z
  (@one_cat_difference_cospan_transf B C C1 Prod t A T0 X Y Z f g) (@one_cat_product_family_pair B C C1 Prod
  (@additive_binary_products C Prod t A) Y X Y (@zero_arrow_family_zero_transf B C t (@additive_terminal_object C
  Prod t A) T0 Y X) (@id (Functor_cat B C) Y)))) (@comp_fapp0 (Functor_cat B C) Y (@fapp0 (Functor_cat B
  (Product_cat C C)) (Functor_cat B C) (@comp_cat_cov_func B (Product_cat C C) C Prod) (@Struct_sigma (Functor B
  C) (λ _ : τ (Functor B C), Functor B C) X Y)) V (@comp_fapp0 (Functor_cat B C) (@fapp0 (Functor_cat B
  (Product_cat C C)) (Functor_cat B C) (@comp_cat_cov_func B (Product_cat C C) C Prod) (@Struct_sigma (Functor B
  C) (λ _ : τ (Functor B C), Functor B C) X Y)) Z V h (@one_cat_difference_cospan_transf B C C1 Prod t A T0
  X Y Z f g)) (@one_cat_product_family_pair B C C1 Prod (@additive_binary_products C Prod t A) Y X Y
  (@zero_arrow_family_zero_transf B C t (@additive_terminal_object C Prod t A) T0 Y X) (@id (Functor_cat B C) Y)))
  (@zero_arrow_family_zero_transf B C t (@additive_terminal_object C Prod t A) T0 Y V) (@comp_assoc (Functor_cat B
  C) Y (@fapp0 (Functor_cat B (Product_cat C C)) (Functor_cat B C) (@comp_cat_cov_func B (Product_cat C C) C Prod)
  (@Struct_sigma (Functor B C) (λ _ : τ (Functor B C), Functor B C) X Y)) Z V h
  (@one_cat_difference_cospan_transf B C C1 Prod t A T0 X Y Z f g) (@one_cat_product_family_pair B C C1 Prod
  (@additive_binary_products C Prod t A) Y X Y (@zero_arrow_family_zero_transf B C t (@additive_terminal_object C
  Prod t A) T0 Y X) (@id (Functor_cat B C) Y))) (@eq_trans (@Transf B C Y V) (@comp_fapp0 (Functor_cat B C) Y
  (@fapp0 (Functor_cat B (Product_cat C C)) (Functor_cat B C) (@comp_cat_cov_func B (Product_cat C C) C Prod)
  (@Struct_sigma (Functor B C) (λ _ : τ (Functor B C), Functor B C) X Y)) V (@comp_fapp0 (Functor_cat B C) (@fapp0
  (Functor_cat B (Product_cat C C)) (Functor_cat B C) (@comp_cat_cov_func B (Product_cat C C) C Prod)
  (@Struct_sigma (Functor B C) (λ _ : τ (Functor B C), Functor B C) X Y)) Z V h
  (@one_cat_difference_cospan_transf B C C1 Prod t A T0 X Y Z f g)) (@one_cat_product_family_pair B C C1
  Prod (@additive_binary_products C Prod t A) Y X Y (@zero_arrow_family_zero_transf B C t
  (@additive_terminal_object C Prod t A) T0 Y X) (@id (Functor_cat B C) Y))) (@comp_fapp0 (Functor_cat B C) Y
  (@fapp0 (Functor_cat B (Product_cat C C)) (Functor_cat B C) (@comp_cat_cov_func B (Product_cat C C) C Prod)
  (@Struct_sigma (Functor B C) (λ _ : τ (Functor B C), Functor B C) X Y)) V (@zero_arrow_family_zero_transf B C t
  (@additive_terminal_object C Prod t A) T0 (@fapp0 (Functor_cat B (Product_cat C C)) (Functor_cat B C)
  (@comp_cat_cov_func B (Product_cat C C) C Prod) (@Struct_sigma (Functor B C) (λ _ : τ (Functor B C), Functor B
  C) X Y)) V) (@one_cat_product_family_pair B C C1 Prod (@additive_binary_products C Prod t A) Y X Y
  (@zero_arrow_family_zero_transf B C t (@additive_terminal_object C Prod t A) T0 Y X) (@id (Functor_cat B C) Y)))
  (@zero_arrow_family_zero_transf B C t (@additive_terminal_object C Prod t A) T0 Y V) (@eq_ap (@Transf B C
  (@fapp0 (Functor_cat B (Product_cat C C)) (Functor_cat B C) (@comp_cat_cov_func B (Product_cat C C) C Prod)
  (@Struct_sigma (Functor B C) (λ _ : τ (Functor B C), Functor B C) X Y)) V) (@Transf B C Y V) (λ u : τ (@Transf B
  C (@fapp0 (Functor_cat B (Product_cat C C)) (Functor_cat B C) (@comp_cat_cov_func B (Product_cat C C) C Prod)
  (@Struct_sigma (Functor B C) (λ _ : τ (Functor B C), Functor B C) X Y)) V), (@comp_fapp0 (Functor_cat B C) Y
  (@fapp0 (Functor_cat B (Product_cat C C)) (Functor_cat B C) (@comp_cat_cov_func B (Product_cat C C) C Prod)
  (@Struct_sigma (Functor B C) (λ _ : τ (Functor B C), Functor B C) X Y)) V u (@one_cat_product_family_pair B C C1
  Prod (@additive_binary_products C Prod t A) Y X Y (@zero_arrow_family_zero_transf B C t
  (@additive_terminal_object C Prod t A) T0 Y X) (@id (Functor_cat B C) Y)))) (@comp_fapp0 (Functor_cat B C)
  (@fapp0 (Functor_cat B (Product_cat C C)) (Functor_cat B C) (@comp_cat_cov_func B (Product_cat C C) C Prod)
  (@Struct_sigma (Functor B C) (λ _ : τ (Functor B C), Functor B C) X Y)) Z V h
  (@one_cat_difference_cospan_transf B C C1 Prod t A T0 X Y Z f g)) (@zero_arrow_family_zero_transf B C t
  (@additive_terminal_object C Prod t A) T0 (@fapp0 (Functor_cat B (Product_cat C C)) (Functor_cat B C)
  (@comp_cat_cov_func B (Product_cat C C) C Prod) (@Struct_sigma (Functor B C) (λ _ : τ (Functor B C), Functor B
  C) X Y)) V) z) (@one_cat_zero_family_precompose_path B C C1 t (@additive_terminal_object C Prod t A) T0 Y
  (@fapp0 (Functor_cat B (Product_cat C C)) (Functor_cat B C) (@comp_cat_cov_func B (Product_cat C C) C Prod)
  (@Struct_sigma (Functor B C) (λ _ : τ (Functor B C), Functor B C) X Y)) V (@one_cat_product_family_pair B C C1
  Prod (@additive_binary_products C Prod t A) Y X Y (@zero_arrow_family_zero_transf B C t
  (@additive_terminal_object C Prod t A) T0 Y X) (@id (Functor_cat B C) Y)))))))) (@eq_trans (@Transf B C Y V)
  (@comp_fapp0 (Functor_cat B C) Y Z V h (@comp_fapp0 (Functor_cat B C) Y X Z f (@zero_arrow_family_zero_transf B
  C t (@additive_terminal_object C Prod t A) T0 Y X))) (@comp_fapp0 (Functor_cat B C) Y Z V h
  (@zero_arrow_family_zero_transf B C t (@additive_terminal_object C Prod t A) T0 Y Z))
  (@zero_arrow_family_zero_transf B C t (@additive_terminal_object C Prod t A) T0 Y V) (@eq_ap (@Transf B C Y Z)
  (@Transf B C Y V) (λ u : τ (@Transf B C Y Z), (@comp_fapp0 (Functor_cat B C) Y Z V h u)) (@comp_fapp0
  (Functor_cat B C) Y X Z f (@zero_arrow_family_zero_transf B C t (@additive_terminal_object C Prod t A) T0 Y X))
  (@zero_arrow_family_zero_transf B C t (@additive_terminal_object C Prod t A) T0 Y Z)
  (@one_cat_zero_family_postcompose_path B C C1 t (@additive_terminal_object C Prod t A) T0 Y X Z f))
  (@one_cat_zero_family_postcompose_path B C C1 t (@additive_terminal_object C Prod t A) T0 Y Z V h)));
