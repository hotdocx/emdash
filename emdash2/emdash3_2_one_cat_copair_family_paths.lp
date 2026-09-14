/* Point observations of the whole native coproduct program at the original data. */
require open emdash.emdash3_2_one_cat_copair_families;
require open emdash.emdash3_2_strict_transfor_component_paths;
require open emdash.emdash3_2_whiskering_component_paths;

// The old scalar copair follows from the whole product projections' naturality.
symbol one_cat_codiagonal_product_map_path [C : Cat] (C1 : τ (IsNCat (cat_succ cat_zero) C))
  [Prod : τ (Functor (Product_cat C C) C)] [t : τ (Obj C)] (A : τ (@AdditiveCategory C Prod t))
  (X Y Z : τ (Obj C)) (f : τ (Hom C X Z)) (g : τ (Hom C Y Z))
  : τ (@= (Hom C (@fapp0 (Product_cat C C) C Prod (@Product_pair C C X Y)) Z) (@comp_fapp0 C (@fapp0 (Product_cat C C)
    C Prod (@Product_pair C C X Y)) (@fapp0 (Product_cat C C) C Prod (@Product_pair C C Z Z)) Z
    (@additive_copair_fapp0 C Prod t A Z Z Z (@id C Z) (@id C Z)) (@fapp1_fapp0 (Product_cat C C) C Prod
    (@Product_pair C C X Y) (@Product_pair C C Z Z) (@Product_pair (Hom_cat C X Z) (Hom_cat C Y Z) f g)))
    (@additive_copair_fapp0 C Prod t A X Y Z f g))
≔ @eq_trans (Hom C (@fapp0 (Product_cat C C) C Prod (@Product_pair C C X Y)) Z) (@comp_fapp0 C (@fapp0 (Product_cat C
  C) C Prod (@Product_pair C C X Y)) (@fapp0 (Product_cat C C) C Prod (@Product_pair C C Z Z)) Z
  (@additive_copair_fapp0 C Prod t A Z Z Z (@id C Z) (@id C Z)) (@fapp1_fapp0 (Product_cat C C) C Prod (@Product_pair
  C C X Y) (@Product_pair C C Z Z) (@Product_pair (Hom_cat C X Z) (Hom_cat C Y Z) f g))) (@preadditive_hom_add C
  (@additive_preadditive C Prod t A) (@fapp0 (Product_cat C C) C Prod (@Product_pair C C X Y)) Z (@comp_fapp0 C
  (@fapp0 (Product_cat C C) C Prod (@Product_pair C C X Y)) (@fapp0 (Product_cat C C) C Prod (@Product_pair C C Z Z))
  Z (@binary_products_proj1_fapp0 C Prod (@additive_binary_products C Prod t A) Z Z) (@fapp1_fapp0 (Product_cat C C) C
  Prod (@Product_pair C C X Y) (@Product_pair C C Z Z) (@Product_pair (Hom_cat C X Z) (Hom_cat C Y Z) f g)))
  (@comp_fapp0 C (@fapp0 (Product_cat C C) C Prod (@Product_pair C C X Y)) (@fapp0 (Product_cat C C) C Prod
  (@Product_pair C C Z Z)) Z (@binary_products_proj2_fapp0 C Prod (@additive_binary_products C Prod t A) Z Z)
  (@fapp1_fapp0 (Product_cat C C) C Prod (@Product_pair C C X Y) (@Product_pair C C Z Z) (@Product_pair (Hom_cat C X
  Z) (Hom_cat C Y Z) f g)))) (@additive_copair_fapp0 C Prod t A X Y Z f g)
    ((@preadditive_comp_add_left_law C (@additive_preadditive C Prod t A)) (@fapp0 (Product_cat C C) C Prod
      (@Product_pair C C X Y)) (@fapp0 (Product_cat C C) C Prod (@Product_pair C C Z Z)) Z
      (@binary_products_proj1_fapp0 C Prod (@additive_binary_products C Prod t A) Z Z) (@binary_products_proj2_fapp0 C
      Prod (@additive_binary_products C Prod t A) Z Z) (@fapp1_fapp0 (Product_cat C C) C Prod (@Product_pair C C X Y)
      (@Product_pair C C Z Z) (@Product_pair (Hom_cat C X Z) (Hom_cat C Y Z) f g)))
    (@additive_add_congr_path C Prod t A (@fapp0 (Product_cat C C) C Prod (@Product_pair C C X Y)) Z
      (@comp_fapp0 C (@fapp0 (Product_cat C C) C Prod (@Product_pair C C X Y)) (@fapp0 (Product_cat C C) C Prod
        (@Product_pair C C Z Z)) Z (@binary_products_proj1_fapp0 C Prod (@additive_binary_products C Prod t A) Z Z)
        (@fapp1_fapp0 (Product_cat C C) C Prod (@Product_pair C C X Y) (@Product_pair C C Z Z) (@Product_pair (Hom_cat
        C X Z) (Hom_cat C Y Z) f g))) (@comp_fapp0 C (@fapp0 (Product_cat C C) C Prod (@Product_pair C C X Y)) X Z f
        (@binary_products_proj1_fapp0 C Prod (@additive_binary_products C Prod t A) X Y))
      (@comp_fapp0 C (@fapp0 (Product_cat C C) C Prod (@Product_pair C C X Y)) (@fapp0 (Product_cat C C) C Prod
        (@Product_pair C C Z Z)) Z (@binary_products_proj2_fapp0 C Prod (@additive_binary_products C Prod t A) Z Z)
        (@fapp1_fapp0 (Product_cat C C) C Prod (@Product_pair C C X Y) (@Product_pair C C Z Z) (@Product_pair (Hom_cat
        C X Z) (Hom_cat C Y Z) f g))) (@comp_fapp0 C (@fapp0 (Product_cat C C) C Prod (@Product_pair C C X Y)) Y Z g
        (@binary_products_proj2_fapp0 C Prod (@additive_binary_products C Prod t A) X Y))
      (@eq_sym (Hom C (@fapp0 (Product_cat C C) C Prod (@Product_pair C C X Y)) Z) (@comp_fapp0 C (@fapp0 (Product_cat
        C C) C Prod (@Product_pair C C X Y)) X Z f (@binary_products_proj1_fapp0 C Prod (@additive_binary_products C
        Prod t A) X Y)) (@comp_fapp0 C (@fapp0 (Product_cat C C) C Prod (@Product_pair C C X Y)) (@fapp0 (Product_cat
        C C) C Prod (@Product_pair C C Z Z)) Z (@binary_products_proj1_fapp0 C Prod (@additive_binary_products C Prod
        t A) Z Z) (@fapp1_fapp0 (Product_cat C C) C Prod (@Product_pair C C X Y) (@Product_pair C C Z Z)
        (@Product_pair (Hom_cat C X Z) (Hom_cat C Y Z) f g))) (@strict_component_naturality_path (Product_cat C C) C
        Prod (@Product_projL_func C C) (@binary_products_proj1_transf C Prod (@additive_binary_products C Prod t A))
        (@Product_pair C C X Y) (@Product_pair C C Z Z) (@Product_pair (Hom_cat C X Z) (Hom_cat C Y Z) f g))) (@eq_sym
        (Hom C (@fapp0 (Product_cat C C) C Prod (@Product_pair C C X Y)) Z) (@comp_fapp0 C (@fapp0 (Product_cat C C) C
        Prod (@Product_pair C C X Y)) Y Z g (@binary_products_proj2_fapp0 C Prod (@additive_binary_products C Prod t
        A) X Y)) (@comp_fapp0 C (@fapp0 (Product_cat C C) C Prod (@Product_pair C C X Y)) (@fapp0 (Product_cat C C) C
        Prod (@Product_pair C C Z Z)) Z (@binary_products_proj2_fapp0 C Prod (@additive_binary_products C Prod t A) Z
        Z) (@fapp1_fapp0 (Product_cat C C) C Prod (@Product_pair C C X Y) (@Product_pair C C Z Z) (@Product_pair
        (Hom_cat C X Z) (Hom_cat C Y Z) f g))) (@strict_component_naturality_path (Product_cat C C) C Prod
        (@Product_projR_func C C) (@binary_products_proj2_transf C Prod (@additive_binary_products C Prod t A))
        (@Product_pair C C X Y) (@Product_pair C C Z Z) (@Product_pair (Hom_cat C X Z) (Hom_cat C Y Z) f g))));

// The whole copair is the native counit/action formula at the same original Prod.
symbol one_cat_copair_family_formula_path [B C : Cat] (C1 : τ (IsNCat (cat_succ cat_zero) C))
  [Prod : τ (Functor (Product_cat C C) C)] [t : τ (Obj C)]
  (A : τ (@AdditiveCategory C Prod t)) (T0 : τ (@TerminalObject (Op_cat C) t)) (X Y Z : τ (Functor B C))
  (f : τ (@Transf B C X Z)) (g : τ (@Transf B C Y Z))
  : τ (@= (@Transf B C (@fapp0 (Functor_cat B (Product_cat C C)) (Functor_cat B C) (@comp_cat_cov_func B (Product_cat
    C C) C Prod) (@Struct_sigma (Functor B C) (λ _ : τ (Functor B C), Functor B C) X Y)) Z)
    (@one_cat_copair_family B C C1 Prod t A T0 X Y Z f g) (@comp_fapp0 (Functor_cat B C) (@fapp0 (Functor_cat B
    (Product_cat C C)) (Functor_cat B C) (@comp_cat_cov_func B (Product_cat C C) C Prod) (@Struct_sigma (Functor B C)
    (λ _ : τ (Functor B C), Functor B C) X Y)) (@comp_cat_fapp0 B (Product_cat C C) C Prod (@comp_cat_fapp0 B C
    (Product_cat C C) (@product_diagonal_func C) Z)) Z (@fapp0 _ _ (@comp_cat_con_fapp1_func B C C Z (@comp_cat_fapp0
    C (Product_cat C C) C Prod (@product_diagonal_func C)) (@id_func C)) (@counit_adj_transf (Product_cat C C) C Prod
    (@product_diagonal_func C) (@one_cat_biproduct_adjunction C C1 Prod t A T0))) (@fapp0 _ _
    (@comp_cat_cov_fapp1_func B (Product_cat C C) C Prod (@Struct_sigma (Functor B C) (λ _ : τ (Functor B C), Functor
    B C) X Y) (@comp_cat_fapp0 B C (Product_cat C C) (@product_diagonal_func C) Z)) (@Struct_sigma (@Transf B C X Z)
    (λ _ : τ (@Transf B C X Z), @Transf B C Y Z) f g))))
≔ @one_cat_adjunction_family_untranspose_agrees B (Product_cat C C) C (@one_cat_product_category C C C1 C1) C1 Prod
  (@product_diagonal_func C) (@one_cat_biproduct_adjunction C C1 Prod t A T0)
    (@Struct_sigma (Functor B C) (λ _ : τ (Functor B C), Functor B C) X Y) Z (@Struct_sigma (@Transf B C X Z) (λ _ : τ
      (@Transf B C X Z), @Transf B C Y Z) f g);

// Original component copairing is recovered through the staged whole component laws.
symbol one_cat_copair_family_component_path [B C : Cat] (C1 : τ (IsNCat (cat_succ cat_zero) C))
  [Prod : τ (Functor (Product_cat C C) C)] [t : τ (Obj C)]
  (A : τ (@AdditiveCategory C Prod t)) (T0 : τ (@TerminalObject (Op_cat C) t)) (X Y Z : τ (Functor B C))
  (f : τ (@Transf B C X Z)) (g : τ (@Transf B C Y Z)) (b : τ (Obj B))
  : τ (@= (Hom C (@fapp0 (Product_cat C C) C Prod (@Product_pair C C (@fapp0 B C X b) (@fapp0 B C Y b))) (@fapp0 B C Z
    b)) (@tapp0_fapp0 B C (@fapp0 (Functor_cat B (Product_cat C C)) (Functor_cat B C) (@comp_cat_cov_func B
    (Product_cat C C) C Prod) (@Struct_sigma (Functor B C) (λ _ : τ (Functor B C), Functor B C) X Y)) Z b
    (@one_cat_copair_family B C C1 Prod t A T0 X Y Z f g)) (@additive_copair_fapp0 C Prod t A (@fapp0 B C X b)
    (@fapp0 B C Y b) (@fapp0 B C Z b) (@tapp0_fapp0 B C X Z b f) (@tapp0_fapp0 B C Y Z b g)))
≔ @eq_trans (Hom C (@fapp0 (Product_cat C C) C Prod (@Product_pair C C (@fapp0 B C X b) (@fapp0 B C Y b))) (@fapp0 B C
  Z b)) (@tapp0_fapp0 B C (@fapp0 (Functor_cat B (Product_cat C C)) (Functor_cat B C) (@comp_cat_cov_func B
  (Product_cat C C) C Prod) (@Struct_sigma (Functor B C) (λ _ : τ (Functor B C), Functor B C) X Y)) Z b
  (@one_cat_copair_family B C C1 Prod t A T0 X Y Z f g)) (@comp_fapp0 C (@fapp0 (Product_cat C C) C Prod
  (@Product_pair C C (@fapp0 B C X b) (@fapp0 B C Y b))) (@fapp0 (Product_cat C C) C Prod (@Product_pair C C (@fapp0 B
  C Z b) (@fapp0 B C Z b))) (@fapp0 B C Z b) (@additive_copair_fapp0 C Prod t A (@fapp0 B C Z b) (@fapp0 B C Z b)
  (@fapp0 B C Z b) (@id C (@fapp0 B C Z b)) (@id C (@fapp0 B C Z b))) (@fapp1_fapp0 (Product_cat C C) C Prod
  (@Product_pair C C (@fapp0 B C X b) (@fapp0 B C Y b)) (@Product_pair C C (@fapp0 B C Z b) (@fapp0 B C Z b))
  (@Product_pair (Hom_cat C (@fapp0 B C X b) (@fapp0 B C Z b)) (Hom_cat C (@fapp0 B C Y b) (@fapp0 B C Z b))
  (@tapp0_fapp0 B C X Z b f) (@tapp0_fapp0 B C Y Z b g))))
    (@additive_copair_fapp0 C Prod t A (@fapp0 B C X b) (@fapp0 B C Y b) (@fapp0 B C Z b) (@tapp0_fapp0 B C X Z b f)
      (@tapp0_fapp0 B C Y Z b g))
    (@eq_trans (Hom C (@fapp0 (Product_cat C C) C Prod (@Product_pair C C (@fapp0 B C X b) (@fapp0 B C Y b))) (@fapp0
      B C Z b)) (@tapp0_fapp0 B C (@fapp0 (Functor_cat B (Product_cat C C)) (Functor_cat B C) (@comp_cat_cov_func B
      (Product_cat C C) C Prod) (@Struct_sigma (Functor B C) (λ _ : τ (Functor B C), Functor B C) X Y)) Z b
      (@one_cat_copair_family B C C1 Prod t A T0 X Y Z f g)) (@comp_fapp0 C (@fapp0 (Product_cat C C) C Prod
      (@Product_pair C C (@fapp0 B C X b) (@fapp0 B C Y b))) (@fapp0 (Product_cat C C) C Prod (@Product_pair C C
      (@fapp0 B C Z b) (@fapp0 B C Z b))) (@fapp0 B C Z b) (@tapp0_fapp0 B C (@comp_cat_fapp0 B (Product_cat C C) C
      Prod (@comp_cat_fapp0 B C (Product_cat C C) (@product_diagonal_func C) Z)) Z b (@fapp0 _ _
      (@comp_cat_con_fapp1_func B C C Z (@comp_cat_fapp0 C (Product_cat C C) C Prod (@product_diagonal_func C))
      (@id_func C)) (@counit_adj_transf (Product_cat C C) C Prod (@product_diagonal_func C)
      (@one_cat_biproduct_adjunction C C1 Prod t A T0)))) (@tapp0_fapp0 B C (@fapp0 (Functor_cat B (Product_cat
      C C)) (Functor_cat B C) (@comp_cat_cov_func B (Product_cat C C) C Prod) (@Struct_sigma (Functor B C) (λ _ : τ
      (Functor B C), Functor B C) X Y)) (@comp_cat_fapp0 B (Product_cat C C) C Prod (@comp_cat_fapp0 B C (Product_cat
      C C) (@product_diagonal_func C) Z)) b (@fapp0 _ _ (@comp_cat_cov_fapp1_func B (Product_cat C C) C Prod
      (@Struct_sigma (Functor B C) (λ _ : τ (Functor B C), Functor B C) X Y) (@comp_cat_fapp0 B C (Product_cat C C)
      (@product_diagonal_func C) Z)) (@Struct_sigma (@Transf B C X Z) (λ _ : τ (@Transf B C X Z), @Transf B C Y Z) f
      g)))) (@comp_fapp0 C (@fapp0 (Product_cat C C) C Prod (@Product_pair C C (@fapp0 B C X b) (@fapp0 B C Y b)))
      (@fapp0 (Product_cat C C) C Prod (@Product_pair C C (@fapp0 B C Z b) (@fapp0 B C Z b))) (@fapp0 B C Z b)
      (@additive_copair_fapp0 C Prod t A (@fapp0 B C Z b) (@fapp0 B C Z b) (@fapp0 B C Z b) (@id C (@fapp0 B C Z b))
      (@id C (@fapp0 B C Z b))) (@fapp1_fapp0 (Product_cat C C) C Prod (@Product_pair C C (@fapp0 B C X b) (@fapp0 B C
      Y b)) (@Product_pair C C (@fapp0 B C Z b) (@fapp0 B C Z b)) (@Product_pair (Hom_cat C (@fapp0 B C X b) (@fapp0 B
      C Z b)) (Hom_cat C (@fapp0 B C Y b) (@fapp0 B C Z b)) (@tapp0_fapp0 B C X Z b f) (@tapp0_fapp0 B C Y Z b g))))
      (@eq_ap (@Transf B C (@fapp0 (Functor_cat B (Product_cat C C)) (Functor_cat B C) (@comp_cat_cov_func B
        (Product_cat C C) C Prod) (@Struct_sigma (Functor B C) (λ _ : τ (Functor B C), Functor B C) X Y)) Z) (Hom C
        (@fapp0 (Product_cat C C) C Prod (@Product_pair C C (@fapp0 B C X b) (@fapp0 B C Y b))) (@fapp0 B C Z b)) (λ h
        : τ (@Transf B C (@fapp0 (Functor_cat B (Product_cat C C)) (Functor_cat B C) (@comp_cat_cov_func B
        (Product_cat C C) C Prod) (@Struct_sigma (Functor B C) (λ _ : τ (Functor B C), Functor B C) X Y)) Z),
        @tapp0_fapp0 B C (@fapp0 (Functor_cat B (Product_cat C C)) (Functor_cat B C) (@comp_cat_cov_func B
        (Product_cat C C) C Prod) (@Struct_sigma (Functor B C) (λ _ : τ (Functor B C), Functor B C) X Y)) Z b h)
        (@one_cat_copair_family B C C1 Prod t A T0 X Y Z f g) (@comp_fapp0 (Functor_cat B C) (@fapp0
        (Functor_cat B (Product_cat C C)) (Functor_cat B C) (@comp_cat_cov_func B (Product_cat C C) C Prod)
        (@Struct_sigma (Functor B C) (λ _ : τ (Functor B C), Functor B C) X Y)) (@comp_cat_fapp0 B (Product_cat C C) C
        Prod (@comp_cat_fapp0 B C (Product_cat C C) (@product_diagonal_func C) Z)) Z (@fapp0 _ _
        (@comp_cat_con_fapp1_func B C C Z (@comp_cat_fapp0 C (Product_cat C C) C Prod (@product_diagonal_func C))
        (@id_func C)) (@counit_adj_transf (Product_cat C C) C Prod (@product_diagonal_func C)
        (@one_cat_biproduct_adjunction C C1 Prod t A T0))) (@fapp0 _ _ (@comp_cat_cov_fapp1_func B (Product_cat
        C C) C Prod (@Struct_sigma (Functor B C) (λ _ : τ (Functor B C), Functor B C) X Y) (@comp_cat_fapp0 B C
        (Product_cat C C) (@product_diagonal_func C) Z)) (@Struct_sigma (@Transf B C X Z) (λ _ : τ (@Transf B C X Z),
        @Transf B C Y Z) f g))) (@one_cat_copair_family_formula_path B C C1 Prod t A T0 X Y Z f g))
      (@eq_trans (Hom C (@fapp0 (Product_cat C C) C Prod (@Product_pair C C (@fapp0 B C X b) (@fapp0 B C Y b)))
        (@fapp0 B C Z b)) (@comp_fapp0 C (@fapp0 (Product_cat C C) C Prod (@Product_pair C C (@fapp0 B C X b) (@fapp0
        B C Y b))) (@fapp0 (Product_cat C C) C Prod (@Product_pair C C (@fapp0 B C Z b) (@fapp0 B C Z b))) (@fapp0 B C
        Z b) (@tapp0_fapp0 B C (@comp_cat_fapp0 B (Product_cat C C) C Prod (@comp_cat_fapp0 B C (Product_cat C C)
        (@product_diagonal_func C) Z)) Z b (@fapp0 _ _ (@comp_cat_con_fapp1_func B C C Z (@comp_cat_fapp0 C
        (Product_cat C C) C Prod (@product_diagonal_func C)) (@id_func C)) (@counit_adj_transf (Product_cat C C) C
        Prod (@product_diagonal_func C) (@one_cat_biproduct_adjunction C C1 Prod t A T0)))) (@tapp0_fapp0 B C
        (@fapp0 (Functor_cat B (Product_cat C C)) (Functor_cat B C) (@comp_cat_cov_func B (Product_cat C C) C Prod)
        (@Struct_sigma (Functor B C) (λ _ : τ (Functor B C), Functor B C) X Y)) (@comp_cat_fapp0 B (Product_cat C C) C
        Prod (@comp_cat_fapp0 B C (Product_cat C C) (@product_diagonal_func C) Z)) b (@fapp0 _ _
        (@comp_cat_cov_fapp1_func B (Product_cat C C) C Prod (@Struct_sigma (Functor B C) (λ _ : τ (Functor B C),
        Functor B C) X Y) (@comp_cat_fapp0 B C (Product_cat C C) (@product_diagonal_func C) Z)) (@Struct_sigma
        (@Transf B C X Z) (λ _ : τ (@Transf B C X Z), @Transf B C Y Z) f g)))) (@comp_fapp0 C (@fapp0 (Product_cat C
        C) C Prod (@Product_pair C C (@fapp0 B C X b) (@fapp0 B C Y b))) (@fapp0 (Product_cat C C) C Prod
        (@Product_pair C C (@fapp0 B C Z b) (@fapp0 B C Z b))) (@fapp0 B C Z b) (@additive_copair_fapp0 C Prod t A
        (@fapp0 B C Z b) (@fapp0 B C Z b) (@fapp0 B C Z b) (@id C (@fapp0 B C Z b)) (@id C (@fapp0 B C Z b)))
        (@fapp1_fapp0 (Product_cat C C) C Prod (@Product_pair C C (@fapp0 B C X b) (@fapp0 B C Y b)) (@Product_pair C
        C (@fapp0 B C Z b) (@fapp0 B C Z b)) (@tapp0_fapp0 B (Product_cat C C) (@Struct_sigma (Functor B C) (λ _ : τ
        (Functor B C), Functor B C) X Y) (@comp_cat_fapp0 B C (Product_cat C C) (@product_diagonal_func C) Z) b
        (@Struct_sigma (@Transf B C X Z) (λ _ : τ (@Transf B C X Z), @Transf B C Y Z) f g)))) (@comp_fapp0 C (@fapp0
        (Product_cat C C) C Prod (@Product_pair C C (@fapp0 B C X b) (@fapp0 B C Y b))) (@fapp0 (Product_cat C C) C
        Prod (@Product_pair C C (@fapp0 B C Z b) (@fapp0 B C Z b))) (@fapp0 B C Z b) (@additive_copair_fapp0 C Prod t
        A (@fapp0 B C Z b) (@fapp0 B C Z b) (@fapp0 B C Z b) (@id C (@fapp0 B C Z b)) (@id C (@fapp0 B C Z b)))
        (@fapp1_fapp0 (Product_cat C C) C Prod (@Product_pair C C (@fapp0 B C X b) (@fapp0 B C Y b)) (@Product_pair C
        C (@fapp0 B C Z b) (@fapp0 B C Z b)) (@Product_pair (Hom_cat C (@fapp0 B C X b) (@fapp0 B C Z b)) (Hom_cat C
        (@fapp0 B C Y b) (@fapp0 B C Z b)) (@tapp0_fapp0 B C X Z b f) (@tapp0_fapp0 B C Y Z b g)))) (@eq_trans (Hom C
        (@fapp0 (Product_cat C C) C Prod (@Product_pair C C (@fapp0 B C X b) (@fapp0 B C Y b))) (@fapp0 B C Z b))
        (@comp_fapp0 C (@fapp0 (Product_cat C C) C Prod (@Product_pair C C (@fapp0 B C X b) (@fapp0 B C Y b))) (@fapp0
        (Product_cat C C) C Prod (@Product_pair C C (@fapp0 B C Z b) (@fapp0 B C Z b))) (@fapp0 B C Z b) (@tapp0_fapp0
        B C (@comp_cat_fapp0 B (Product_cat C C) C Prod (@comp_cat_fapp0 B C (Product_cat C C) (@product_diagonal_func
        C) Z)) Z b (@fapp0 _ _ (@comp_cat_con_fapp1_func B C C Z (@comp_cat_fapp0 C (Product_cat C C) C Prod
        (@product_diagonal_func C)) (@id_func C)) (@counit_adj_transf (Product_cat C C) C Prod (@product_diagonal_func
        C) (@one_cat_biproduct_adjunction C C1 Prod t A T0)))) (@tapp0_fapp0 B C (@fapp0 (Functor_cat B
        (Product_cat C C)) (Functor_cat B C) (@comp_cat_cov_func B (Product_cat C C) C Prod) (@Struct_sigma (Functor B
        C) (λ _ : τ (Functor B C), Functor B C) X Y)) (@comp_cat_fapp0 B (Product_cat C C) C Prod (@comp_cat_fapp0 B C
        (Product_cat C C) (@product_diagonal_func C) Z)) b (@fapp0 _ _ (@comp_cat_cov_fapp1_func B (Product_cat C C) C
        Prod (@Struct_sigma (Functor B C) (λ _ : τ (Functor B C), Functor B C) X Y) (@comp_cat_fapp0 B C (Product_cat
        C C) (@product_diagonal_func C) Z)) (@Struct_sigma (@Transf B C X Z) (λ _ : τ (@Transf B C X Z), @Transf B C Y
        Z) f g)))) (@comp_fapp0 C (@fapp0 (Product_cat C C) C Prod (@Product_pair C C (@fapp0 B C X b) (@fapp0 B C Y
        b))) (@fapp0 (Product_cat C C) C Prod (@Product_pair C C (@fapp0 B C Z b) (@fapp0 B C Z b))) (@fapp0 B C Z b)
        (@additive_copair_fapp0 C Prod t A (@fapp0 B C Z b) (@fapp0 B C Z b) (@fapp0 B C Z b) (@id C (@fapp0 B C Z b))
        (@id C (@fapp0 B C Z b))) (@tapp0_fapp0 B C (@fapp0 (Functor_cat B (Product_cat C C)) (Functor_cat B C)
        (@comp_cat_cov_func B (Product_cat C C) C Prod) (@Struct_sigma (Functor B C) (λ _ : τ (Functor B C), Functor B
        C) X Y)) (@comp_cat_fapp0 B (Product_cat C C) C Prod (@comp_cat_fapp0 B C (Product_cat C C)
        (@product_diagonal_func C) Z)) b (@fapp0 _ _ (@comp_cat_cov_fapp1_func B (Product_cat C C) C Prod
        (@Struct_sigma (Functor B C) (λ _ : τ (Functor B C), Functor B C) X Y) (@comp_cat_fapp0 B C (Product_cat C C)
        (@product_diagonal_func C) Z)) (@Struct_sigma (@Transf B C X Z) (λ _ : τ (@Transf B C X Z), @Transf B C Y Z) f
        g)))) (@comp_fapp0 C (@fapp0 (Product_cat C C) C Prod (@Product_pair C C (@fapp0 B C X b) (@fapp0 B C Y b)))
        (@fapp0 (Product_cat C C) C Prod (@Product_pair C C (@fapp0 B C Z b) (@fapp0 B C Z b))) (@fapp0 B C Z b)
        (@additive_copair_fapp0 C Prod t A (@fapp0 B C Z b) (@fapp0 B C Z b) (@fapp0 B C Z b) (@id C (@fapp0 B C Z b))
        (@id C (@fapp0 B C Z b))) (@fapp1_fapp0 (Product_cat C C) C Prod (@Product_pair C C (@fapp0 B C X b) (@fapp0 B
        C Y b)) (@Product_pair C C (@fapp0 B C Z b) (@fapp0 B C Z b)) (@tapp0_fapp0 B (Product_cat C C) (@Struct_sigma
        (Functor B C) (λ _ : τ (Functor B C), Functor B C) X Y) (@comp_cat_fapp0 B C (Product_cat C C)
        (@product_diagonal_func C) Z) b (@Struct_sigma (@Transf B C X Z) (λ _ : τ (@Transf B C X Z), @Transf B C Y Z)
        f g)))) (@eq_ap (Hom C (@fapp0 (Product_cat C C) C Prod (@Product_pair C C (@fapp0 B C Z b) (@fapp0 B C Z b)))
        (@fapp0 B C Z b)) (Hom C (@fapp0 (Product_cat C C) C Prod (@Product_pair C C (@fapp0 B C X b) (@fapp0 B C Y
        b))) (@fapp0 B C Z b)) (λ v : τ (Hom C (@fapp0 (Product_cat C C) C Prod (@Product_pair C C (@fapp0 B C Z b)
        (@fapp0 B C Z b))) (@fapp0 B C Z b)), (@comp_fapp0 C (@fapp0 (Product_cat C C) C Prod (@Product_pair C C
        (@fapp0 B C X b) (@fapp0 B C Y b))) (@fapp0 (Product_cat C C) C Prod (@Product_pair C C (@fapp0 B C Z b)
        (@fapp0 B C Z b))) (@fapp0 B C Z b) v (@tapp0_fapp0 B C (@fapp0 (Functor_cat B (Product_cat C C)) (Functor_cat
        B C) (@comp_cat_cov_func B (Product_cat C C) C Prod) (@Struct_sigma (Functor B C) (λ _ : τ (Functor B C),
        Functor B C) X Y)) (@comp_cat_fapp0 B (Product_cat C C) C Prod (@comp_cat_fapp0 B C (Product_cat C C)
        (@product_diagonal_func C) Z)) b (@fapp0 _ _ (@comp_cat_cov_fapp1_func B (Product_cat C C) C Prod
        (@Struct_sigma (Functor B C) (λ _ : τ (Functor B C), Functor B C) X Y) (@comp_cat_fapp0 B C (Product_cat C C)
        (@product_diagonal_func C) Z)) (@Struct_sigma (@Transf B C X Z) (λ _ : τ (@Transf B C X Z), @Transf B C Y Z) f
        g))))) (@tapp0_fapp0 B C (@comp_cat_fapp0 B (Product_cat C C) C Prod (@comp_cat_fapp0 B C (Product_cat C C)
        (@product_diagonal_func C) Z)) Z b (@fapp0 _ _ (@comp_cat_con_fapp1_func B C C Z (@comp_cat_fapp0 C
        (Product_cat C C) C Prod (@product_diagonal_func C)) (@id_func C)) (@counit_adj_transf (Product_cat C C) C
        Prod (@product_diagonal_func C) (@one_cat_biproduct_adjunction C C1 Prod t A T0))))
        (@additive_copair_fapp0 C Prod t A (@fapp0 B C Z b) (@fapp0 B C Z b) (@fapp0 B C Z b) (@id C (@fapp0 B C Z b))
        (@id C (@fapp0 B C Z b))) (@prewhisker_component_path B C C Z (@comp_cat_fapp0 C (Product_cat C C) C
        Prod (@product_diagonal_func C)) (@id_func C) (@counit_adj_transf (Product_cat C C) C Prod
        (@product_diagonal_func C) (@one_cat_biproduct_adjunction C C1 Prod t A T0)) b)) (@eq_ap (Hom C (@fapp0
        (Product_cat C C) C Prod (@Product_pair C C (@fapp0 B C X b) (@fapp0 B C Y b))) (@fapp0 (Product_cat C C) C
        Prod (@Product_pair C C (@fapp0 B C Z b) (@fapp0 B C Z b)))) (Hom C (@fapp0 (Product_cat C C) C Prod
        (@Product_pair C C (@fapp0 B C X b) (@fapp0 B C Y b))) (@fapp0 B C Z b)) (λ v : τ (Hom C (@fapp0 (Product_cat
        C C) C Prod (@Product_pair C C (@fapp0 B C X b) (@fapp0 B C Y b))) (@fapp0 (Product_cat C C) C Prod
        (@Product_pair C C (@fapp0 B C Z b) (@fapp0 B C Z b)))), (@comp_fapp0 C (@fapp0 (Product_cat C C) C Prod
        (@Product_pair C C (@fapp0 B C X b) (@fapp0 B C Y b))) (@fapp0 (Product_cat C C) C Prod (@Product_pair C C
        (@fapp0 B C Z b) (@fapp0 B C Z b))) (@fapp0 B C Z b) (@additive_copair_fapp0 C Prod t A (@fapp0 B C Z b)
        (@fapp0 B C Z b) (@fapp0 B C Z b) (@id C (@fapp0 B C Z b)) (@id C (@fapp0 B C Z b))) v)) (@tapp0_fapp0 B C
        (@fapp0 (Functor_cat B (Product_cat C C)) (Functor_cat B C) (@comp_cat_cov_func B (Product_cat C C) C Prod)
        (@Struct_sigma (Functor B C) (λ _ : τ (Functor B C), Functor B C) X Y)) (@comp_cat_fapp0 B (Product_cat C C) C
        Prod (@comp_cat_fapp0 B C (Product_cat C C) (@product_diagonal_func C) Z)) b (@fapp0 _ _
        (@comp_cat_cov_fapp1_func B (Product_cat C C) C Prod (@Struct_sigma (Functor B C) (λ _ : τ (Functor B C),
        Functor B C) X Y) (@comp_cat_fapp0 B C (Product_cat C C) (@product_diagonal_func C) Z)) (@Struct_sigma
        (@Transf B C X Z) (λ _ : τ (@Transf B C X Z), @Transf B C Y Z) f g))) (@fapp1_fapp0 (Product_cat C C) C Prod
        (@Product_pair C C (@fapp0 B C X b) (@fapp0 B C Y b)) (@Product_pair C C (@fapp0 B C Z b) (@fapp0 B C Z b))
        (@tapp0_fapp0 B (Product_cat C C) (@Struct_sigma (Functor B C) (λ _ : τ (Functor B C), Functor B C) X Y)
        (@comp_cat_fapp0 B C (Product_cat C C) (@product_diagonal_func C) Z) b (@Struct_sigma (@Transf B C X Z) (λ _ :
        τ (@Transf B C X Z), @Transf B C Y Z) f g))) (@postwhisker_native_source_component_path B (Product_cat C
        C) C Prod (@Struct_sigma (Functor B C) (λ _ : τ (Functor B C), Functor B C) X Y) (@comp_cat_fapp0 B C
        (Product_cat C C) (@product_diagonal_func C) Z) (@Struct_sigma (@Transf B C X Z) (λ _ : τ (@Transf B C X Z),
        @Transf B C Y Z) f g) b))) (@eq_ap (Hom (Product_cat C C) (@Product_pair C C (@fapp0 B C X b) (@fapp0 B C Y
        b)) (@Product_pair C C (@fapp0 B C Z b) (@fapp0 B C Z b))) (Hom C (@fapp0 (Product_cat C C) C Prod
        (@Product_pair C C (@fapp0 B C X b) (@fapp0 B C Y b))) (@fapp0 B C Z b)) (λ v : τ (Hom (Product_cat C C)
        (@Product_pair C C (@fapp0 B C X b) (@fapp0 B C Y b)) (@Product_pair C C (@fapp0 B C Z b) (@fapp0 B C Z b))),
        (@comp_fapp0 C (@fapp0 (Product_cat C C) C Prod (@Product_pair C C (@fapp0 B C X b) (@fapp0 B C Y b))) (@fapp0
        (Product_cat C C) C Prod (@Product_pair C C (@fapp0 B C Z b) (@fapp0 B C Z b))) (@fapp0 B C Z b)
        (@additive_copair_fapp0 C Prod t A (@fapp0 B C Z b) (@fapp0 B C Z b) (@fapp0 B C Z b) (@id C (@fapp0 B C Z b))
        (@id C (@fapp0 B C Z b))) (@fapp1_fapp0 (Product_cat C C) C Prod (@Product_pair C C (@fapp0 B C X b) (@fapp0 B
        C Y b)) (@Product_pair C C (@fapp0 B C Z b) (@fapp0 B C Z b)) v))) (@tapp0_fapp0 B (Product_cat C C)
        (@Struct_sigma (Functor B C) (λ _ : τ (Functor B C), Functor B C) X Y) (@comp_cat_fapp0 B C (Product_cat C C)
        (@product_diagonal_func C) Z) b (@Struct_sigma (@Transf B C X Z) (λ _ : τ (@Transf B C X Z), @Transf B C Y Z)
        f g)) (@Product_pair (Hom_cat C (@fapp0 B C X b) (@fapp0 B C Z b)) (Hom_cat C (@fapp0 B C Y b) (@fapp0 B C Z
        b)) (@tapp0_fapp0 B C X Z b f) (@tapp0_fapp0 B C Y Z b g)) (@eq_refl (Hom (Product_cat C C) (@Product_pair C C
        (@fapp0 B C X b) (@fapp0 B C Y b)) (@Product_pair C C (@fapp0 B C Z b) (@fapp0 B C Z b))) (@tapp0_fapp0 B
        (Product_cat C C) (@Struct_sigma (Functor B C) (λ _ : τ (Functor B C), Functor B C) X Y) (@comp_cat_fapp0 B C
        (Product_cat C C) (@product_diagonal_func C) Z) b (@Struct_sigma (@Transf B C X Z) (λ _ : τ (@Transf B C X Z),
        @Transf B C Y Z) f g))))))
    (@one_cat_codiagonal_product_map_path C C1 Prod t A (@fapp0 B C X b) (@fapp0 B C Y b) (@fapp0 B C Z b)
      (@tapp0_fapp0 B C X Z b f) (@tapp0_fapp0 B C Y Z b g));
