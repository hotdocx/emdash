/* Whole product pairing through the original P and lifted Δ⊣P.
   Native endpoints are retained inside mate applications; the product of
   transformation categories is the public proof-time view.
   No pointwise naturality input or new product selection is supplied. */
require open emdash.emdash3_2_one_cat_product_adjunction;
require open emdash.emdash3_2_one_cat_adjunction_family_views;

// Native first-class pairing, now with all three endpoint families varying over B.
symbol one_cat_product_family_pair_func [B C : Cat]
  (C1 : τ (IsNCat (cat_succ cat_zero) C)) [P : τ (Functor (Product_cat C C) C)]
  (BP : τ (@BinaryProducts C P)) (X F G : τ (Functor B C))
  : τ (Functor
      (Product_cat (@Transf_cat B C X F) (@Transf_cat B C X G))
      (@Transf_cat B C X (@fapp0 (Functor_cat B (Product_cat C C)) (Functor_cat B C)
        (@comp_cat_cov_func B (Product_cat C C) C P) (Struct_sigma F G))))
≔ @one_cat_adjunction_family_transpose_func B C (Product_cat C C)
    C1 (@one_cat_product_category C C C1 C1) (@product_diagonal_func C) P
    (@one_cat_binary_product_adjunction C C1 P BP) X (Struct_sigma F G);

// The inverse is a whole pair of maps, not a pointwise field reconstruction.
symbol one_cat_product_family_unpair_func [B C : Cat]
  (C1 : τ (IsNCat (cat_succ cat_zero) C)) [P : τ (Functor (Product_cat C C) C)]
  (BP : τ (@BinaryProducts C P)) (X F G : τ (Functor B C))
  : τ (Functor
      (@Transf_cat B C X (@fapp0 (Functor_cat B (Product_cat C C)) (Functor_cat B C)
        (@comp_cat_cov_func B (Product_cat C C) C P) (Struct_sigma F G)))
      (Product_cat (@Transf_cat B C X F) (@Transf_cat B C X G)))
≔ @one_cat_adjunction_family_untranspose_func B C (Product_cat C C)
    C1 (@one_cat_product_category C C C1 C1) (@product_diagonal_func C) P
    (@one_cat_binary_product_adjunction C C1 P BP) X (Struct_sigma F G);

symbol one_cat_product_family_pair [B C : Cat]
  (C1 : τ (IsNCat (cat_succ cat_zero) C)) [P : τ (Functor (Product_cat C C) C)]
  (BP : τ (@BinaryProducts C P))
  (X F G : τ (Functor B C)) (f : τ (@Transf B C X F)) (g : τ (@Transf B C X G))
  : τ (@Transf B C X (@fapp0 (Functor_cat B (Product_cat C C)) (Functor_cat B C)
      (@comp_cat_cov_func B (Product_cat C C) C P) (Struct_sigma F G)))
≔ @fapp0 (Hom_cat (Functor_cat B (Product_cat C C))
      (@fapp0 _ _ (@comp_cat_cov_func B C (Product_cat C C) (@product_diagonal_func C)) X)
      (Struct_sigma F G)) (@Transf_cat B C X (@fapp0 (Functor_cat B (Product_cat C C)) (Functor_cat B C)
      (@comp_cat_cov_func B (Product_cat C C) C P) (Struct_sigma F G)))
    (@one_cat_product_family_pair_func B C C1 P BP X F G)
    (@Struct_sigma (@Transf B C X F) (λ _ : τ (@Transf B C X F), @Transf B C X G) f g);

symbol one_cat_product_family_unpair [B C : Cat]
  (C1 : τ (IsNCat (cat_succ cat_zero) C)) [P : τ (Functor (Product_cat C C) C)]
  (BP : τ (@BinaryProducts C P)) (X F G : τ (Functor B C))
  (h : τ (@Transf B C X (@fapp0 (Functor_cat B (Product_cat C C)) (Functor_cat B C)
    (@comp_cat_cov_func B (Product_cat C C) C P) (Struct_sigma F G))))
  : τ (Obj (Product_cat (@Transf_cat B C X F) (@Transf_cat B C X G)))
≔ @fapp0 (@Transf_cat B C X (@fapp0 (Functor_cat B (Product_cat C C)) (Functor_cat B C)
      (@comp_cat_cov_func B (Product_cat C C) C P) (Struct_sigma F G))) (Hom_cat (Functor_cat B (Product_cat C C))
      (@fapp0 _ _ (@comp_cat_cov_func B C (Product_cat C C) (@product_diagonal_func C)) X)
      (Struct_sigma F G))
    (@one_cat_product_family_unpair_func B C C1 P BP X F G) h;


// Whole mate formula, observed through the same selected comparison.
symbol one_cat_product_family_pair_formula_path [B C : Cat] (C1 : τ (IsNCat (cat_succ cat_zero) C))
  [P : τ (Functor (Product_cat C C) C)] (BP : τ (@BinaryProducts C P))
  (X F G : τ (Functor B C)) (f : τ (@Transf B C X F)) (g : τ (@Transf B C X G))
  : τ (@= (@Transf B C X (@fapp0 (Functor_cat B (Product_cat C C)) (Functor_cat B C) (@comp_cat_cov_func B
    (Product_cat C C) C P) (@Struct_sigma (Functor B C) (λ _ : τ (Functor B C), Functor B C) F G)))
    (@one_cat_product_family_pair B C C1 P BP X F G f g) (@comp_fapp0 (Functor_cat B C) X (@comp_cat_fapp0 B
    (Product_cat C C) C P (@comp_cat_fapp0 B C (Product_cat C C) (@product_diagonal_func C) X)) (@fapp0 (Functor_cat B
    (Product_cat C C)) (Functor_cat B C) (@comp_cat_cov_func B (Product_cat C C) C P) (@Struct_sigma (Functor B C) (λ
    _ : τ (Functor B C), Functor B C) F G)) (@fapp0 _ _ (@comp_cat_cov_fapp1_func B (Product_cat C C) C P
    (@comp_cat_fapp0 B C (Product_cat C C) (@product_diagonal_func C) X) (@Struct_sigma (Functor B C) (λ _ : τ (Functor
    B C), Functor B C) F G)) (@Struct_sigma (@Transf B C X F) (λ _ : τ (@Transf B C X F), @Transf B C X G) f g))
    (@fapp0 _ _ (@comp_cat_con_fapp1_func B C C X (@id_func C) (@comp_cat_fapp0 C (Product_cat C C) C P
    (@product_diagonal_func C))) (@unit_adj_transf C (Product_cat C C) (@product_diagonal_func C) P
    (@one_cat_binary_product_adjunction C C1 P BP)))))
≔ @one_cat_adjunction_family_transpose_agrees B C (Product_cat C C) C1 (@one_cat_product_category C C C1 C1)
  (@product_diagonal_func C) P (@one_cat_binary_product_adjunction C C1 P BP) X (@Struct_sigma (Functor B C) (λ _ : τ (Functor B
  C), Functor B C) F G) (@Struct_sigma (@Transf B C X F) (λ _ : τ (@Transf B C X F), @Transf B C X G) f g);

// The selected old pairing is recovered as an observation of the same whole native mate.
symbol one_cat_product_family_pair_component_path [B C : Cat] (C1 : τ (IsNCat (cat_succ cat_zero) C))
  [P : τ (Functor (Product_cat C C) C)] (BP : τ (@BinaryProducts C P))
  (X F G : τ (Functor B C)) (f : τ (@Transf B C X F)) (g : τ (@Transf B C X G)) (b : τ (Obj B))
  : τ (@= (Hom C (@fapp0 B C X b) (@fapp0 (Product_cat C C) C P (@Product_pair C C (@fapp0 B C F b) (@fapp0 B C G
    b)))) (@tapp0_fapp0 B C X (@fapp0 (Functor_cat B (Product_cat C C)) (Functor_cat B C) (@comp_cat_cov_func B
    (Product_cat C C) C P) (@Struct_sigma (Functor B C) (λ _ : τ (Functor B C), Functor B C) F G)) b
    (@one_cat_product_family_pair B C C1 P BP X F G f g)) (@binary_products_pair_fapp0 C P BP (@fapp0 B C X b) (@fapp0 B
    C F b) (@fapp0 B C G b) (@tapp0_fapp0 B C X F b f) (@tapp0_fapp0 B C X G b g)))
≔ @eq_trans (Hom C (@fapp0 B C X b) (@fapp0 (Product_cat C C) C P (@Product_pair C C (@fapp0 B C F b) (@fapp0 B C G
  b)))) (@tapp0_fapp0 B C X (@fapp0 (Functor_cat B (Product_cat C C)) (Functor_cat B C) (@comp_cat_cov_func B
  (Product_cat C C) C P) (@Struct_sigma (Functor B C) (λ _ : τ (Functor B C), Functor B C) F G)) b
  (@one_cat_product_family_pair B C C1 P BP X F G f g)) (@comp_fapp0 C (@fapp0 B C X b) (@fapp0 (Product_cat C C) C P
  (@Product_pair C C (@fapp0 B C X b) (@fapp0 B C X b))) (@fapp0 (Product_cat C C) C P (@Product_pair C C (@fapp0 B C
  F b) (@fapp0 B C G b))) (@fapp1_fapp0 (Product_cat C C) C P (@Product_pair C C (@fapp0 B C X b) (@fapp0 B C X b))
  (@Product_pair C C (@fapp0 B C F b) (@fapp0 B C G b)) (@tapp0_fapp0 B (Product_cat C C) (@comp_cat_fapp0 B C
  (Product_cat C C) (@product_diagonal_func C) X) (@Struct_sigma (Functor B C) (λ _ : τ (Functor B C), Functor B C) F G)
  b (@Struct_sigma (@Transf B C X F) (λ _ : τ (@Transf B C X F), @Transf B C X G) f g))) (@binary_products_pair_fapp0
  C P BP (@fapp0 B C X b) (@fapp0 B C X b) (@fapp0 B C X b) (@id C (@fapp0 B C X b)) (@id C (@fapp0 B C X b))))
  (@binary_products_pair_fapp0 C P BP (@fapp0 B C X b) (@fapp0 B C F b) (@fapp0 B C G b) (@tapp0_fapp0 B C X F b f)
  (@tapp0_fapp0 B C X G b g))
    (@eq_ap (@Transf B C X (@fapp0 (Functor_cat B (Product_cat C C)) (Functor_cat B C) (@comp_cat_cov_func B
      (Product_cat C C) C P) (@Struct_sigma (Functor B C) (λ _ : τ (Functor B C), Functor B C) F G))) (Hom C (@fapp0 B
      C X b) (@fapp0 (Product_cat C C) C P (@Product_pair C C (@fapp0 B C F b) (@fapp0 B C G b))))
      (λ k : τ (@Transf B C X (@fapp0 (Functor_cat B (Product_cat C C)) (Functor_cat B C) (@comp_cat_cov_func B
        (Product_cat C C) C P) (@Struct_sigma (Functor B C) (λ _ : τ (Functor B C), Functor B C) F G))), @tapp0_fapp0
        B C X (@fapp0 (Functor_cat B (Product_cat C C)) (Functor_cat B C) (@comp_cat_cov_func B (Product_cat C C) C P)
        (@Struct_sigma (Functor B C) (λ _ : τ (Functor B C), Functor B C) F G)) b k) (@one_cat_product_family_pair B C
        C1 P BP X F G f g) (@comp_fapp0 (Functor_cat B C) X (@comp_cat_fapp0 B (Product_cat C C) C P (@comp_cat_fapp0
        B C (Product_cat C C) (@product_diagonal_func C) X)) (@fapp0 (Functor_cat B (Product_cat C C)) (Functor_cat B C)
        (@comp_cat_cov_func B (Product_cat C C) C P) (@Struct_sigma (Functor B C) (λ _ : τ (Functor B C), Functor B C)
        F G)) (@fapp0 _ _ (@comp_cat_cov_fapp1_func B (Product_cat C C) C P (@comp_cat_fapp0 B C (Product_cat C C)
        (@product_diagonal_func C) X) (@Struct_sigma (Functor B C) (λ _ : τ (Functor B C), Functor B C) F G))
        (@Struct_sigma (@Transf B C X F) (λ _ : τ (@Transf B C X F), @Transf B C X G) f g)) (@fapp0 _ _
        (@comp_cat_con_fapp1_func B C C X (@id_func C) (@comp_cat_fapp0 C (Product_cat C C) C P (@product_diagonal_func
        C))) (@unit_adj_transf C (Product_cat C C) (@product_diagonal_func C) P (@one_cat_binary_product_adjunction C C1 P BP))))
      (@one_cat_product_family_pair_formula_path B C C1 P BP X F G f g))
    (@eq_trans (Hom C (@fapp0 B C X b) (@fapp0 (Product_cat C C) C P (@Product_pair C C (@fapp0 B C F b) (@fapp0 B C G
      b)))) (@comp_fapp0 C (@fapp0 B C X b) (@fapp0 (Product_cat C C) C P (@Product_pair C C (@fapp0 B C X b) (@fapp0
      B C X b))) (@fapp0 (Product_cat C C) C P (@Product_pair C C (@fapp0 B C F b) (@fapp0 B C G b))) (@fapp1_fapp0
      (Product_cat C C) C P (@Product_pair C C (@fapp0 B C X b) (@fapp0 B C X b)) (@Product_pair C C (@fapp0 B C F b)
      (@fapp0 B C G b)) (@tapp0_fapp0 B (Product_cat C C) (@comp_cat_fapp0 B C (Product_cat C C) (@product_diagonal_func
      C) X) (@Struct_sigma (Functor B C) (λ _ : τ (Functor B C), Functor B C) F G) b (@Struct_sigma (@Transf B C X F)
      (λ _ : τ (@Transf B C X F), @Transf B C X G) f g))) (@binary_products_pair_fapp0 C P BP (@fapp0 B C X b) (@fapp0
      B C X b) (@fapp0 B C X b) (@id C (@fapp0 B C X b)) (@id C (@fapp0 B C X b)))) (@comp_fapp0 C (@fapp0 B C X b)
      (@fapp0 (Product_cat C C) C P (@Product_pair C C (@fapp0 B C X b) (@fapp0 B C X b))) (@fapp0 (Product_cat C C) C
      P (@Product_pair C C (@fapp0 B C F b) (@fapp0 B C G b))) (@fapp1_fapp0 (Product_cat C C) C P (@Product_pair C C
      (@fapp0 B C X b) (@fapp0 B C X b)) (@Product_pair C C (@fapp0 B C F b) (@fapp0 B C G b)) (@Product_pair (Hom_cat
      C (@fapp0 B C X b) (@fapp0 B C F b)) (Hom_cat C (@fapp0 B C X b) (@fapp0 B C G b)) (@tapp0_fapp0 B C X F b f)
      (@tapp0_fapp0 B C X G b g))) (@binary_products_pair_fapp0 C P BP (@fapp0 B C X b) (@fapp0 B C X b) (@fapp0 B C X
      b) (@id C (@fapp0 B C X b)) (@id C (@fapp0 B C X b)))) (@binary_products_pair_fapp0 C P BP (@fapp0 B C X b)
      (@fapp0 B C F b) (@fapp0 B C G b) (@tapp0_fapp0 B C X F b f) (@tapp0_fapp0 B C X G b g))
      (@eq_ap (Hom (Product_cat C C) (@Product_pair C C (@fapp0 B C X b) (@fapp0 B C X b)) (@Product_pair C C (@fapp0
        B C F b) (@fapp0 B C G b))) (Hom C (@fapp0 B C X b) (@fapp0 (Product_cat C C) C P (@Product_pair C C (@fapp0 B
        C F b) (@fapp0 B C G b))))
        (λ v : τ (Hom (Product_cat C C) (@Product_pair C C (@fapp0 B C X b) (@fapp0 B C X b)) (@Product_pair C C
          (@fapp0 B C F b) (@fapp0 B C G b))), @comp_fapp0 C (@fapp0 B C X b) (@fapp0 (Product_cat C C) C P
          (@Product_pair C C (@fapp0 B C X b) (@fapp0 B C X b))) (@fapp0 (Product_cat C C) C P (@Product_pair C C
          (@fapp0 B C F b) (@fapp0 B C G b)))
          (@fapp1_fapp0 (Product_cat C C) C P (@Product_pair C C (@fapp0 B C X b) (@fapp0 B C X b)) (@Product_pair C C
            (@fapp0 B C F b) (@fapp0 B C G b)) v) (@binary_products_pair_fapp0 C P BP (@fapp0 B C X b) (@fapp0 B C X
            b) (@fapp0 B C X b) (@id C (@fapp0 B C X b)) (@id C (@fapp0 B C X b))))
        (@tapp0_fapp0 B (Product_cat C C) (@comp_cat_fapp0 B C (Product_cat C C) (@product_diagonal_func C) X)
          (@Struct_sigma (Functor B C) (λ _ : τ (Functor B C), Functor B C) F G) b (@Struct_sigma (@Transf B C X F) (λ
          _ : τ (@Transf B C X F), @Transf B C X G) f g)) (@Product_pair (Hom_cat C (@fapp0 B C X b) (@fapp0 B C F b))
          (Hom_cat C (@fapp0 B C X b) (@fapp0 B C G b)) (@tapp0_fapp0 B C X F b f) (@tapp0_fapp0 B C X G b g))
        (@eq_refl (Hom (Product_cat C C) (@Product_pair C C (@fapp0 B C X b) (@fapp0 B C X b)) (@Product_pair C C
          (@fapp0 B C F b) (@fapp0 B C G b))) (@tapp0_fapp0 B (Product_cat C C) (@comp_cat_fapp0 B C (Product_cat C C)
          (@product_diagonal_func C) X) (@Struct_sigma (Functor B C) (λ _ : τ (Functor B C), Functor B C) F G) b
          (@Struct_sigma (@Transf B C X F) (λ _ : τ (@Transf B C X F), @Transf B C X G) f g))))
      (@eq_ap (Hom C (@fapp0 (Product_cat C C) C P (@Product_pair C C (@fapp0 B C X b) (@fapp0 B C X b))) (@fapp0
        (Product_cat C C) C P (@Product_pair C C (@fapp0 B C F b) (@fapp0 B C G b)))) (Hom C (@fapp0 B C X b) (@fapp0
        (Product_cat C C) C P (@Product_pair C C (@fapp0 B C F b) (@fapp0 B C G b))))
        (λ k : τ (Hom C (@fapp0 (Product_cat C C) C P (@Product_pair C C (@fapp0 B C X b) (@fapp0 B C X b))) (@fapp0
          (Product_cat C C) C P (@Product_pair C C (@fapp0 B C F b) (@fapp0 B C G b)))), @comp_fapp0 C (@fapp0 B C X
          b) (@fapp0 (Product_cat C C) C P (@Product_pair C C (@fapp0 B C X b) (@fapp0 B C X b))) (@fapp0 (Product_cat
          C C) C P (@Product_pair C C (@fapp0 B C F b) (@fapp0 B C G b))) k (@binary_products_pair_fapp0 C P BP
          (@fapp0 B C X b) (@fapp0 B C X b) (@fapp0 B C X b) (@id C (@fapp0 B C X b)) (@id C (@fapp0 B C X b))))
          (@fapp1_fapp0 (Product_cat C C) C P (@Product_pair C C (@fapp0 B C X b) (@fapp0 B C X b)) (@Product_pair C C
          (@fapp0 B C F b) (@fapp0 B C G b)) (@Product_pair (Hom_cat C (@fapp0 B C X b) (@fapp0 B C F b)) (Hom_cat C
          (@fapp0 B C X b) (@fapp0 B C G b)) (@tapp0_fapp0 B C X F b f) (@tapp0_fapp0 B C X G b g)))
          (@binary_products_map_fapp0 C P BP (@fapp0 B C X b) (@fapp0 B C F b) (@fapp0 B C X b) (@fapp0 B C G b)
          (@tapp0_fapp0 B C X F b f) (@tapp0_fapp0 B C X G b g))
        (@binary_products_map_path C P BP (@fapp0 B C X b) (@fapp0 B C F b) (@fapp0 B C X b) (@fapp0 B C G b)
          (@tapp0_fapp0 B C X F b f) (@tapp0_fapp0 B C X G b g))));
