/* Whole native product/coproduct laws preserve original maps and selections. */
require open emdash.emdash3_2_one_cat_product_family_projection_paths;
require open emdash.emdash3_2_one_cat_biproduct_family_distribution;

assert [B C : Cat] (C1 : τ (IsNCat (cat_succ cat_zero) C)) [Prod : τ (Functor (Product_cat C C) C)] (BP : τ
  (@BinaryProducts C Prod)) (X F G : τ (Functor B C)) (f : τ (@Transf B C X F)) (g : τ (@Transf B C X G)) ⊢
  @one_cat_product_family_pair_proj1_path B C C1 Prod BP X F G f g : τ (@= (@Transf B C X F) (@comp_fapp0 (Functor_cat
  B C) X (@fapp0 (Functor_cat B (Product_cat C C)) (Functor_cat B C) (@comp_cat_cov_func B (Product_cat C C) C Prod)
  (@Struct_sigma (Functor B C) (λ _ : τ (Functor B C), Functor B C) F G)) F (@one_cat_product_family_proj1 B C C1 Prod
  BP F G) (@one_cat_product_family_pair B C C1 Prod BP X F G f g)) f);
assert [B C : Cat] (C1 : τ (IsNCat (cat_succ cat_zero) C)) [Prod : τ (Functor (Product_cat C C) C)] (BP : τ
  (@BinaryProducts C Prod)) (X F G : τ (Functor B C)) (f : τ (@Transf B C X F)) (g : τ (@Transf B C X G)) ⊢
  @one_cat_product_family_pair_proj2_path B C C1 Prod BP X F G f g : τ (@= (@Transf B C X G) (@comp_fapp0 (Functor_cat
  B C) X (@fapp0 (Functor_cat B (Product_cat C C)) (Functor_cat B C) (@comp_cat_cov_func B (Product_cat C C) C Prod)
  (@Struct_sigma (Functor B C) (λ _ : τ (Functor B C), Functor B C) F G)) G (@one_cat_product_family_proj2 B C C1 Prod
  BP F G) (@one_cat_product_family_pair B C C1 Prod BP X F G f g)) g);
assert [B C : Cat] (C1 : τ (IsNCat (cat_succ cat_zero) C)) [Prod : τ (Functor (Product_cat C C) C)] (BP : τ
  (@BinaryProducts C Prod)) (X0 X1 F G : τ (Functor B C)) (h : τ (@Transf B C X0 X1)) (f : τ (@Transf B C X1 F)) (g :
  τ (@Transf B C X1 G)) ⊢ @one_cat_product_pair_precompose_path B C C1 Prod BP X0 X1 F G h f g : τ (@= (@Transf B C X0
  (@fapp0 (Functor_cat B (Product_cat C C)) (Functor_cat B C) (@comp_cat_cov_func B (Product_cat C C) C Prod)
  (@Struct_sigma (Functor B C) (λ _ : τ (Functor B C), Functor B C) F G))) (@comp_fapp0 (Functor_cat B C) X0 X1
  (@fapp0 (Functor_cat B (Product_cat C C)) (Functor_cat B C) (@comp_cat_cov_func B (Product_cat C C) C Prod)
  (@Struct_sigma (Functor B C) (λ _ : τ (Functor B C), Functor B C) F G)) (@one_cat_product_family_pair B C C1 Prod BP
  X1 F G f g) h) (@one_cat_product_family_pair B C C1 Prod BP X0 F G (@comp_fapp0 (Functor_cat B C) X0 X1 F f h)
  (@comp_fapp0 (Functor_cat B C) X0 X1 G g h)));
assert [B C : Cat] (C1 : τ (IsNCat (cat_succ cat_zero) C)) [Prod : τ (Functor (Product_cat C C) C)] [t : τ (Obj C)] (A
  : τ (@AdditiveCategory C Prod t)) (T0 : τ (@TerminalObject (Op_cat C) t)) (F G Y Z : τ (Functor B C)) (f : τ
  (@Transf B C F Y)) (g : τ (@Transf B C G Y)) (h : τ (@Transf B C Y Z)) ⊢ @one_cat_copair_postcompose_path B C C1
  Prod t A T0 F G Y Z f g h : τ (@= (@Transf B C (@fapp0 (Functor_cat B (Product_cat C C)) (Functor_cat B C)
  (@comp_cat_cov_func B (Product_cat C C) C Prod) (@Struct_sigma (Functor B C) (λ _ : τ (Functor B C), Functor B C) F
  G)) Z) (@comp_fapp0 (Functor_cat B C) (@fapp0 (Functor_cat B (Product_cat C C)) (Functor_cat B C)
  (@comp_cat_cov_func B (Product_cat C C) C Prod) (@Struct_sigma (Functor B C) (λ _ : τ (Functor B C), Functor B C) F
  G)) Y Z h (@one_cat_copair_family B C C1 Prod t A T0 F G Y f g)) (@one_cat_copair_family B C C1 Prod t A T0 F G Z
  (@comp_fapp0 (Functor_cat B C) F Y Z h f) (@comp_fapp0 (Functor_cat B C) G Y Z h g)));
assert [B C : Cat] (Prod : τ (Functor (Product_cat C C) C)) (F0 G0 F1 G1 : τ (Functor B C)) (u v : τ (Obj (Hom_cat
  (Functor_cat B (Product_cat C C)) (@Struct_sigma (Functor B C) (λ _ : τ (Functor B C), Functor B C) F0 G0)
  (@Struct_sigma (Functor B C) (λ _ : τ (Functor B C), Functor B C) F1 G1)))) ⊢ @fapp1_func (Hom_cat (Functor_cat B
  (Product_cat C C)) (@Struct_sigma (Functor B C) (λ _ : τ (Functor B C), Functor B C) F0 G0) (@Struct_sigma (Functor
  B C) (λ _ : τ (Functor B C), Functor B C) F1 G1)) (@Transf_cat B C (@fapp0 (Functor_cat B (Product_cat C C))
  (Functor_cat B C) (@comp_cat_cov_func B (Product_cat C C) C Prod) (@Struct_sigma (Functor B C) (λ _ : τ (Functor B
  C), Functor B C) F0 G0)) (@fapp0 (Functor_cat B (Product_cat C C)) (Functor_cat B C) (@comp_cat_cov_func B
  (Product_cat C C) C Prod) (@Struct_sigma (Functor B C) (λ _ : τ (Functor B C), Functor B C) F1 G1)))
  (@product_family_map_func B C Prod F0 G0 F1 G1) u v : τ (Functor (Hom_cat (Hom_cat (Functor_cat B (Product_cat C C))
  (@Struct_sigma (Functor B C) (λ _ : τ (Functor B C), Functor B C) F0 G0) (@Struct_sigma (Functor B C) (λ _ : τ
  (Functor B C), Functor B C) F1 G1)) u v) (Hom_cat (@Transf_cat B C (@fapp0 (Functor_cat B (Product_cat C C))
  (Functor_cat B C) (@comp_cat_cov_func B (Product_cat C C) C Prod) (@Struct_sigma (Functor B C) (λ _ : τ (Functor B
  C), Functor B C) F0 G0)) (@fapp0 (Functor_cat B (Product_cat C C)) (Functor_cat B C) (@comp_cat_cov_func B
  (Product_cat C C) C Prod) (@Struct_sigma (Functor B C) (λ _ : τ (Functor B C), Functor B C) F1 G1))) (@fapp0
  (Hom_cat (Functor_cat B (Product_cat C C)) (@Struct_sigma (Functor B C) (λ _ : τ (Functor B C), Functor B C) F0 G0)
  (@Struct_sigma (Functor B C) (λ _ : τ (Functor B C), Functor B C) F1 G1)) (@Transf_cat B C (@fapp0 (Functor_cat B
  (Product_cat C C)) (Functor_cat B C) (@comp_cat_cov_func B (Product_cat C C) C Prod) (@Struct_sigma (Functor B C) (λ
  _ : τ (Functor B C), Functor B C) F0 G0)) (@fapp0 (Functor_cat B (Product_cat C C)) (Functor_cat B C)
  (@comp_cat_cov_func B (Product_cat C C) C Prod) (@Struct_sigma (Functor B C) (λ _ : τ (Functor B C), Functor B C) F1
  G1))) (@product_family_map_func B C Prod F0 G0 F1 G1) u) (@fapp0 (Hom_cat (Functor_cat B (Product_cat C C))
  (@Struct_sigma (Functor B C) (λ _ : τ (Functor B C), Functor B C) F0 G0) (@Struct_sigma (Functor B C) (λ _ : τ
  (Functor B C), Functor B C) F1 G1)) (@Transf_cat B C (@fapp0 (Functor_cat B (Product_cat C C)) (Functor_cat B C)
  (@comp_cat_cov_func B (Product_cat C C) C Prod) (@Struct_sigma (Functor B C) (λ _ : τ (Functor B C), Functor B C) F0
  G0)) (@fapp0 (Functor_cat B (Product_cat C C)) (Functor_cat B C) (@comp_cat_cov_func B (Product_cat C C) C Prod)
  (@Struct_sigma (Functor B C) (λ _ : τ (Functor B C), Functor B C) F1 G1))) (@product_family_map_func B C Prod F0 G0
  F1 G1) v)));
assertnot [B C : Cat] (C1 : τ (IsNCat (cat_succ cat_zero) C)) [Prod : τ (Functor (Product_cat C C) C)] (BP : τ
  (@BinaryProducts C Prod)) (X F G : τ (Functor B C)) (f f0 : τ (@Transf B C X F)) (g : τ (@Transf B C X G)) ⊢
  @eq_refl (@Transf B C X F) f : τ (@= (@Transf B C X F) (@comp_fapp0 (Functor_cat B C) X (@fapp0 (Functor_cat B
  (Product_cat C C)) (Functor_cat B C) (@comp_cat_cov_func B (Product_cat C C) C Prod) (@Struct_sigma (Functor B C) (λ
  _ : τ (Functor B C), Functor B C) F G)) F (@one_cat_product_family_proj1 B C C1 Prod BP F G)
  (@one_cat_product_family_pair B C C1 Prod BP X F G f g)) f0);

// Independent whole coordinates exercise target action beyond the repeated diagonal case.
assert [B C : Cat] (C1 : τ (IsNCat (cat_succ cat_zero) C)) [Prod : τ (Functor (Product_cat C C) C)] (BP : τ
  (@BinaryProducts C Prod)) (X F0 G0 F1 G1 : τ (Functor B C))
  (f : τ (@Transf B C X F0)) (g : τ (@Transf B C X G0))
  (a : τ (@Transf B C F0 F1)) (b : τ (@Transf B C G0 G1))
  ⊢ @one_cat_product_pair_target_path B C C1 Prod BP X F0 G0 F1 G1 f g a b
    : τ (@= (@Transf B C X (@fapp0 (Functor_cat B (Product_cat C C)) (Functor_cat B C) (@comp_cat_cov_func B
  (Product_cat C C) C Prod) (@Struct_sigma (Functor B C) (λ _ : τ (Functor B C), Functor B C) F1 G1))) (@comp_fapp0
  (Functor_cat B C) X (@fapp0 (Functor_cat B (Product_cat C C)) (Functor_cat B C) (@comp_cat_cov_func B (Product_cat C
  C) C Prod) (@Struct_sigma (Functor B C) (λ _ : τ (Functor B C), Functor B C) F0 G0)) (@fapp0 (Functor_cat B
  (Product_cat C C)) (Functor_cat B C) (@comp_cat_cov_func B (Product_cat C C) C Prod) (@Struct_sigma (Functor B C) (λ
  _ : τ (Functor B C), Functor B C) F1 G1)) (@product_family_map B C Prod F0 G0 F1 G1 a b)
  (@one_cat_product_family_pair B C C1 Prod BP X F0 G0 f g)) (@one_cat_product_family_pair B C C1 Prod BP X F1 G1
  (@comp_fapp0 (Functor_cat B C) X F0 F1 a f) (@comp_fapp0 (Functor_cat B C) X G0 G1 b g)));

// The source law likewise retains two different component maps.
assert [B C : Cat] (C1 : τ (IsNCat (cat_succ cat_zero) C)) [Prod : τ (Functor (Product_cat C C) C)] [t : τ (Obj C)] (A
  : τ (@AdditiveCategory C Prod t)) (T0 : τ (@TerminalObject (Op_cat C) t)) (F0 G0 F1 G1 Z : τ (Functor B C))
  (a : τ (@Transf B C F0 F1)) (b : τ (@Transf B C G0 G1))
  (f : τ (@Transf B C F1 Z)) (g : τ (@Transf B C G1 Z))
  ⊢ @one_cat_copair_source_path B C C1 Prod t A T0 F0 G0 F1 G1 Z a b f g
    : τ (@= (@Transf B C (@fapp0 (Functor_cat B (Product_cat C C)) (Functor_cat B C) (@comp_cat_cov_func B
  (Product_cat C C) C Prod) (@Struct_sigma (Functor B C) (λ _ : τ (Functor B C), Functor B C) F0 G0)) Z) (@comp_fapp0
  (Functor_cat B C) (@fapp0 (Functor_cat B (Product_cat C C)) (Functor_cat B C) (@comp_cat_cov_func B (Product_cat C
  C) C Prod) (@Struct_sigma (Functor B C) (λ _ : τ (Functor B C), Functor B C) F0 G0)) (@fapp0 (Functor_cat B
  (Product_cat C C)) (Functor_cat B C) (@comp_cat_cov_func B (Product_cat C C) C Prod) (@Struct_sigma (Functor B C) (λ
  _ : τ (Functor B C), Functor B C) F1 G1)) Z (@one_cat_copair_family B C C1 Prod t A T0 F1 G1 Z f g)
  (@product_family_map B C Prod F0 G0 F1 G1 a b)) (@one_cat_copair_family B C C1 Prod t A T0 F0 G0 Z (@comp_fapp0
  (Functor_cat B C) F0 F1 Z f a) (@comp_fapp0 (Functor_cat B C) G0 G1 Z g b)));
