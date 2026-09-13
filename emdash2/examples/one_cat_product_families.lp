/* Whole inverse computation, original projections and retained higher action. */
require open emdash.emdash3_2_one_cat_product_families;

assert [B C : Cat] (C1 : τ (IsNCat (cat_succ cat_zero) C))
  [P : τ (Functor (Product_cat C C) C)] (BP : τ (@BinaryProducts C P))
  (X F G : τ (Functor B C)) (f : τ (@Transf B C X F)) (g : τ (@Transf B C X G))
  ⊢ @one_cat_product_family_unpair B C C1 P BP X F G (@one_cat_product_family_pair B C C1 P BP X F G f g)
    ≡ @Product_pair (@Transf_cat B C X F) (@Transf_cat B C X G) f g;

assert [B C : Cat] (C1 : τ (IsNCat (cat_succ cat_zero) C))
  [P : τ (Functor (Product_cat C C) C)] (BP : τ (@BinaryProducts C P))
  (X F G : τ (Functor B C))
  (h : τ (@Transf B C X (@fapp0 (Functor_cat B (Product_cat C C)) (Functor_cat B C)
    (@comp_cat_cov_func B (Product_cat C C) C P) (Struct_sigma F G))))
  ⊢ @fapp0 _ _ (@one_cat_product_family_pair_func B C C1 P BP X F G)
      (@one_cat_product_family_unpair B C C1 P BP X F G h) ≡ h;

assert [C : Cat] (C1 : τ (IsNCat (cat_succ cat_zero) C))
  [P : τ (Functor (Product_cat C C) C)] (BP : τ (@BinaryProducts C P)) (X : τ (Obj C))
  ⊢ @tapp0_fapp0 C C (@id_func C) (@comp_cat_fapp0 C (Product_cat C C) C P (@product_diagonal_func C)) X
      (@unit_adj_transf C (Product_cat C C) (@product_diagonal_func C) P (@one_cat_binary_product_adjunction C C1 P
        BP))
    ≡ @binary_products_pair_fapp0 C P BP X X X (@id C X) (@id C X);

// The inverse is a whole functor; both its object and higher actions cancel.
assert [B C : Cat] (C1 : τ (IsNCat (cat_succ cat_zero) C))
  [P : τ (Functor (Product_cat C C) C)] (BP : τ (@BinaryProducts C P))
  (X F G : τ (Functor B C)) ⊢ (@comp_cat_fapp0 (Hom_cat (Functor_cat B (Product_cat C C)) (@fapp0 _ _
    (@comp_cat_cov_func B C (Product_cat C C) (@product_diagonal_func C)) X) (Struct_sigma F G)) (@Transf_cat B C X
    (@fapp0 (Functor_cat B (Product_cat C C)) (Functor_cat B C) (@comp_cat_cov_func B (Product_cat C C) C P)
    (Struct_sigma F G))) (Hom_cat (Functor_cat B (Product_cat C C)) (@fapp0 _ _ (@comp_cat_cov_func B C (Product_cat C
    C) (@product_diagonal_func C)) X) (Struct_sigma F G)) (@one_cat_product_family_unpair_func B C C1 P BP X F G)
    (@one_cat_product_family_pair_func B C C1 P BP X F G)) ≡ @id_func (Hom_cat (Functor_cat B (Product_cat C C))
    (@fapp0 _ _ (@comp_cat_cov_func B C (Product_cat C C) (@product_diagonal_func C)) X) (Struct_sigma F G));
assert [B C : Cat] (C1 : τ (IsNCat (cat_succ cat_zero) C))
  [P : τ (Functor (Product_cat C C) C)] (BP : τ (@BinaryProducts C P))
  (X F G : τ (Functor B C)) (h k : τ (Obj (Hom_cat (Functor_cat B (Product_cat C C)) (@fapp0 _ _ (@comp_cat_cov_func B
    C (Product_cat C C) (@product_diagonal_func C)) X) (Struct_sigma F G))))
  ⊢ @fapp1_func (Hom_cat (Functor_cat B (Product_cat C C)) (@fapp0 _ _ (@comp_cat_cov_func B C (Product_cat C C)
    (@product_diagonal_func C)) X) (Struct_sigma F G)) (Hom_cat (Functor_cat B (Product_cat C C)) (@fapp0 _ _
    (@comp_cat_cov_func B C (Product_cat C C) (@product_diagonal_func C)) X) (Struct_sigma F G)) (@comp_cat_fapp0
    (Hom_cat (Functor_cat B (Product_cat C C)) (@fapp0 _ _ (@comp_cat_cov_func B C (Product_cat C C)
    (@product_diagonal_func C)) X) (Struct_sigma F G)) (@Transf_cat B C X (@fapp0 (Functor_cat B (Product_cat C C))
    (Functor_cat B C) (@comp_cat_cov_func B (Product_cat C C) C P) (Struct_sigma F G))) (Hom_cat (Functor_cat B
    (Product_cat C C)) (@fapp0 _ _ (@comp_cat_cov_func B C (Product_cat C C) (@product_diagonal_func C)) X)
    (Struct_sigma F G)) (@one_cat_product_family_unpair_func B C C1 P BP X F G) (@one_cat_product_family_pair_func B C
    C1 P BP X F G)) h k ≡ @id_func (Hom_cat (Hom_cat (Functor_cat B (Product_cat C C)) (@fapp0 _ _ (@comp_cat_cov_func
    B C (Product_cat C C) (@product_diagonal_func C)) X) (Struct_sigma F G)) h k);
assert [B C : Cat] (C1 : τ (IsNCat (cat_succ cat_zero) C))
  [P : τ (Functor (Product_cat C C) C)] (BP : τ (@BinaryProducts C P))
  (X F G : τ (Functor B C)) (h k : τ (Obj (Hom_cat (Functor_cat B (Product_cat C C)) (@fapp0 _ _ (@comp_cat_cov_func B
    C (Product_cat C C) (@product_diagonal_func C)) X) (Struct_sigma F G)))) (alpha : τ (Hom (Hom_cat (Functor_cat B
    (Product_cat C C)) (@fapp0 _ _ (@comp_cat_cov_func B C (Product_cat C C) (@product_diagonal_func C)) X)
    (Struct_sigma F G)) h k))
  ⊢ @fapp1_fapp0 (Hom_cat (Functor_cat B (Product_cat C C)) (@fapp0 _ _ (@comp_cat_cov_func B C (Product_cat C C)
    (@product_diagonal_func C)) X) (Struct_sigma F G)) (Hom_cat (Functor_cat B (Product_cat C C)) (@fapp0 _ _
    (@comp_cat_cov_func B C (Product_cat C C) (@product_diagonal_func C)) X) (Struct_sigma F G)) (@comp_cat_fapp0
    (Hom_cat (Functor_cat B (Product_cat C C)) (@fapp0 _ _ (@comp_cat_cov_func B C (Product_cat C C)
    (@product_diagonal_func C)) X) (Struct_sigma F G)) (@Transf_cat B C X (@fapp0 (Functor_cat B (Product_cat C C))
    (Functor_cat B C) (@comp_cat_cov_func B (Product_cat C C) C P) (Struct_sigma F G))) (Hom_cat (Functor_cat B
    (Product_cat C C)) (@fapp0 _ _ (@comp_cat_cov_func B C (Product_cat C C) (@product_diagonal_func C)) X)
    (Struct_sigma F G)) (@one_cat_product_family_unpair_func B C C1 P BP X F G) (@one_cat_product_family_pair_func B C
    C1 P BP X F G)) h k alpha ≡ alpha;

// The inverse is a whole functor; both its object and higher actions cancel.
assert [B C : Cat] (C1 : τ (IsNCat (cat_succ cat_zero) C))
  [P : τ (Functor (Product_cat C C) C)] (BP : τ (@BinaryProducts C P))
  (X F G : τ (Functor B C)) ⊢ (@comp_cat_fapp0 (@Transf_cat B C X (@fapp0 (Functor_cat B (Product_cat C C))
    (Functor_cat B C) (@comp_cat_cov_func B (Product_cat C C) C P) (Struct_sigma F G))) (Hom_cat (Functor_cat B
    (Product_cat C C)) (@fapp0 _ _ (@comp_cat_cov_func B C (Product_cat C C) (@product_diagonal_func C)) X)
    (Struct_sigma F G)) (@Transf_cat B C X (@fapp0 (Functor_cat B (Product_cat C C)) (Functor_cat B C)
    (@comp_cat_cov_func B (Product_cat C C) C P) (Struct_sigma F G))) (@one_cat_product_family_pair_func B C C1 P BP X
    F G) (@one_cat_product_family_unpair_func B C C1 P BP X F G)) ≡ @id_func (@Transf_cat B C X (@fapp0 (Functor_cat B
    (Product_cat C C)) (Functor_cat B C) (@comp_cat_cov_func B (Product_cat C C) C P) (Struct_sigma F G)));
assert [B C : Cat] (C1 : τ (IsNCat (cat_succ cat_zero) C))
  [P : τ (Functor (Product_cat C C) C)] (BP : τ (@BinaryProducts C P))
  (X F G : τ (Functor B C)) (h k : τ (Obj (@Transf_cat B C X (@fapp0 (Functor_cat B (Product_cat C C)) (Functor_cat B
    C) (@comp_cat_cov_func B (Product_cat C C) C P) (Struct_sigma F G)))))
  ⊢ @fapp1_func (@Transf_cat B C X (@fapp0 (Functor_cat B (Product_cat C C)) (Functor_cat B C) (@comp_cat_cov_func B
    (Product_cat C C) C P) (Struct_sigma F G))) (@Transf_cat B C X (@fapp0 (Functor_cat B (Product_cat C C))
    (Functor_cat B C) (@comp_cat_cov_func B (Product_cat C C) C P) (Struct_sigma F G))) (@comp_cat_fapp0 (@Transf_cat
    B C X (@fapp0 (Functor_cat B (Product_cat C C)) (Functor_cat B C) (@comp_cat_cov_func B (Product_cat C C) C P)
    (Struct_sigma F G))) (Hom_cat (Functor_cat B (Product_cat C C)) (@fapp0 _ _ (@comp_cat_cov_func B C (Product_cat C
    C) (@product_diagonal_func C)) X) (Struct_sigma F G)) (@Transf_cat B C X (@fapp0 (Functor_cat B (Product_cat C C))
    (Functor_cat B C) (@comp_cat_cov_func B (Product_cat C C) C P) (Struct_sigma F G)))
    (@one_cat_product_family_pair_func B C C1 P BP X F G) (@one_cat_product_family_unpair_func B C C1 P BP X F G)) h k
    ≡ @id_func (Hom_cat (@Transf_cat B C X (@fapp0 (Functor_cat B (Product_cat C C)) (Functor_cat B C)
    (@comp_cat_cov_func B (Product_cat C C) C P) (Struct_sigma F G))) h k);
assert [B C : Cat] (C1 : τ (IsNCat (cat_succ cat_zero) C))
  [P : τ (Functor (Product_cat C C) C)] (BP : τ (@BinaryProducts C P))
  (X F G : τ (Functor B C)) (h k : τ (Obj (@Transf_cat B C X (@fapp0 (Functor_cat B (Product_cat C C)) (Functor_cat B
    C) (@comp_cat_cov_func B (Product_cat C C) C P) (Struct_sigma F G))))) (alpha : τ (Hom (@Transf_cat B C X (@fapp0
    (Functor_cat B (Product_cat C C)) (Functor_cat B C) (@comp_cat_cov_func B (Product_cat C C) C P) (Struct_sigma F
    G))) h k))
  ⊢ @fapp1_fapp0 (@Transf_cat B C X (@fapp0 (Functor_cat B (Product_cat C C)) (Functor_cat B C) (@comp_cat_cov_func B
    (Product_cat C C) C P) (Struct_sigma F G))) (@Transf_cat B C X (@fapp0 (Functor_cat B (Product_cat C C))
    (Functor_cat B C) (@comp_cat_cov_func B (Product_cat C C) C P) (Struct_sigma F G))) (@comp_cat_fapp0 (@Transf_cat
    B C X (@fapp0 (Functor_cat B (Product_cat C C)) (Functor_cat B C) (@comp_cat_cov_func B (Product_cat C C) C P)
    (Struct_sigma F G))) (Hom_cat (Functor_cat B (Product_cat C C)) (@fapp0 _ _ (@comp_cat_cov_func B C (Product_cat C
    C) (@product_diagonal_func C)) X) (Struct_sigma F G)) (@Transf_cat B C X (@fapp0 (Functor_cat B (Product_cat C C))
    (Functor_cat B C) (@comp_cat_cov_func B (Product_cat C C) C P) (Struct_sigma F G)))
    (@one_cat_product_family_pair_func B C C1 P BP X F G) (@one_cat_product_family_unpair_func B C C1 P BP X F G)) h k
    alpha ≡ alpha;

// Recovery includes the original whole transformation and nonidentity base action.
assert [B C : Cat] (C1 : τ (IsNCat (cat_succ cat_zero) C))
  [P : τ (Functor (Product_cat C C) C)] (BP : τ (@BinaryProducts C P))
  (X F G : τ (Functor B C)) (f : τ (@Transf B C X F)) (g : τ (@Transf B C X G)) ⊢ sigma_Fst
    (@one_cat_product_family_unpair B C C1 P BP X F G (@one_cat_product_family_pair B C C1 P BP X F G f g)) ≡ f;
assert [B C : Cat] (C1 : τ (IsNCat (cat_succ cat_zero) C))
  [P : τ (Functor (Product_cat C C) C)] (BP : τ (@BinaryProducts C P))
  (X F G : τ (Functor B C)) (f : τ (@Transf B C X F)) (g : τ (@Transf B C X G)) (b b' : τ (Obj B)) (u : τ (Hom B b
    b'))
  ⊢ @tapp1_fapp0 B C X F b b' (sigma_Fst (@one_cat_product_family_unpair B C C1 P BP X F G
    (@one_cat_product_family_pair B C C1 P BP X F G f g))) u
    ≡ @tapp1_fapp0 B C X F b b' f u;

// Recovery includes the original whole transformation and nonidentity base action.
assert [B C : Cat] (C1 : τ (IsNCat (cat_succ cat_zero) C))
  [P : τ (Functor (Product_cat C C) C)] (BP : τ (@BinaryProducts C P))
  (X F G : τ (Functor B C)) (f : τ (@Transf B C X F)) (g : τ (@Transf B C X G)) ⊢ sigma_Snd
    (@one_cat_product_family_unpair B C C1 P BP X F G (@one_cat_product_family_pair B C C1 P BP X F G f g)) ≡ g;
assert [B C : Cat] (C1 : τ (IsNCat (cat_succ cat_zero) C))
  [P : τ (Functor (Product_cat C C) C)] (BP : τ (@BinaryProducts C P))
  (X F G : τ (Functor B C)) (f : τ (@Transf B C X F)) (g : τ (@Transf B C X G)) (b b' : τ (Obj B)) (u : τ (Hom B b
    b'))
  ⊢ @tapp1_fapp0 B C X G b b' (sigma_Snd (@one_cat_product_family_unpair B C C1 P BP X F G
    (@one_cat_product_family_pair B C C1 P BP X F G f g))) u
    ≡ @tapp1_fapp0 B C X G b b' g u;

// A native inverse must not identify an unrelated whole input.
assertnot [B C : Cat] (C1 : τ (IsNCat (cat_succ cat_zero) C))
  [P : τ (Functor (Product_cat C C) C)] (BP : τ (@BinaryProducts C P))
  (X F G : τ (Functor B C)) (f : τ (@Transf B C X F)) (g : τ (@Transf B C X G)) (f0 : τ (@Transf B C X F))
  ⊢ @eq_refl (@Transf B C X F) (sigma_Fst (@one_cat_product_family_unpair B C C1 P BP X F G
    (@one_cat_product_family_pair B C C1 P BP X F G f g)))
    : τ (@= (@Transf B C X F) (sigma_Fst (@one_cat_product_family_unpair B C C1 P BP X F G
      (@one_cat_product_family_pair B C C1 P BP X F G f g))) f0);

// The original selected projection recovers the original component.
assert [B C : Cat] (C1 : τ (IsNCat (cat_succ cat_zero) C))
  [P : τ (Functor (Product_cat C C) C)] (BP : τ (@BinaryProducts C P))
  (X F G : τ (Functor B C)) (f : τ (@Transf B C X F)) (g : τ (@Transf B C X G)) (b : τ (Obj B))
  ⊢ @eq_ap (Hom C (@fapp0 B C X b) (@fapp0 (Product_cat C C) C P (@Product_pair C C (@fapp0 B C F b) (@fapp0 B C G
    b)))) (Hom C (@fapp0 B C X b) (@fapp0 B C F b))
      (λ k : τ (Hom C (@fapp0 B C X b) (@fapp0 (Product_cat C C) C P (@Product_pair C C (@fapp0 B C F b) (@fapp0 B C G
        b)))), @comp_fapp0 C (@fapp0 B C X b) (@fapp0 (Product_cat C C) C P (@Product_pair C C (@fapp0 B C F b)
        (@fapp0 B C G b))) (@fapp0 B C F b) (@binary_products_proj1_fapp0 C P BP (@fapp0 B C F b) (@fapp0 B C G b)) k)
        (@tapp0_fapp0 B C X (@fapp0 (Functor_cat B (Product_cat C C)) (Functor_cat B C) (@comp_cat_cov_func B
        (Product_cat C C) C P) (Struct_sigma F G)) b (@one_cat_product_family_pair B C C1 P BP X F G f g))
        (@binary_products_pair_fapp0 C P BP (@fapp0 B C X b) (@fapp0 B C F b) (@fapp0 B C G b) (@tapp0_fapp0 B C X F b
        f) (@tapp0_fapp0 B C X G b g)) (@one_cat_product_family_pair_component_path B C C1 P BP X F G f g b)
    : τ (@= (Hom C (@fapp0 B C X b) (@fapp0 B C F b)) (@comp_fapp0 C (@fapp0 B C X b) (@fapp0 (Product_cat C C) C P
      (@Product_pair C C (@fapp0 B C F b) (@fapp0 B C G b))) (@fapp0 B C F b) (@binary_products_proj1_fapp0 C P BP
      (@fapp0 B C F b) (@fapp0 B C G b)) (@tapp0_fapp0 B C X (@fapp0 (Functor_cat B (Product_cat C C)) (Functor_cat B
      C) (@comp_cat_cov_func B (Product_cat C C) C P) (Struct_sigma F G)) b (@one_cat_product_family_pair B C C1 P BP
      X F G f g))) (@tapp0_fapp0 B C X F b f));

// The original selected projection recovers the original component.
assert [B C : Cat] (C1 : τ (IsNCat (cat_succ cat_zero) C))
  [P : τ (Functor (Product_cat C C) C)] (BP : τ (@BinaryProducts C P))
  (X F G : τ (Functor B C)) (f : τ (@Transf B C X F)) (g : τ (@Transf B C X G)) (b : τ (Obj B))
  ⊢ @eq_ap (Hom C (@fapp0 B C X b) (@fapp0 (Product_cat C C) C P (@Product_pair C C (@fapp0 B C F b) (@fapp0 B C G
    b)))) (Hom C (@fapp0 B C X b) (@fapp0 B C G b))
      (λ k : τ (Hom C (@fapp0 B C X b) (@fapp0 (Product_cat C C) C P (@Product_pair C C (@fapp0 B C F b) (@fapp0 B C G
        b)))), @comp_fapp0 C (@fapp0 B C X b) (@fapp0 (Product_cat C C) C P (@Product_pair C C (@fapp0 B C F b)
        (@fapp0 B C G b))) (@fapp0 B C G b) (@binary_products_proj2_fapp0 C P BP (@fapp0 B C F b) (@fapp0 B C G b)) k)
        (@tapp0_fapp0 B C X (@fapp0 (Functor_cat B (Product_cat C C)) (Functor_cat B C) (@comp_cat_cov_func B
        (Product_cat C C) C P) (Struct_sigma F G)) b (@one_cat_product_family_pair B C C1 P BP X F G f g))
        (@binary_products_pair_fapp0 C P BP (@fapp0 B C X b) (@fapp0 B C F b) (@fapp0 B C G b) (@tapp0_fapp0 B C X F b
        f) (@tapp0_fapp0 B C X G b g)) (@one_cat_product_family_pair_component_path B C C1 P BP X F G f g b)
    : τ (@= (Hom C (@fapp0 B C X b) (@fapp0 B C G b)) (@comp_fapp0 C (@fapp0 B C X b) (@fapp0 (Product_cat C C) C P
      (@Product_pair C C (@fapp0 B C F b) (@fapp0 B C G b))) (@fapp0 B C G b) (@binary_products_proj2_fapp0 C P BP
      (@fapp0 B C F b) (@fapp0 B C G b)) (@tapp0_fapp0 B C X (@fapp0 (Functor_cat B (Product_cat C C)) (Functor_cat B
      C) (@comp_cat_cov_func B (Product_cat C C) C P) (Struct_sigma F G)) b (@one_cat_product_family_pair B C C1 P BP
      X F G f g))) (@tapp0_fapp0 B C X G b g));

assert [C : Cat] (C1 : τ (IsNCat (cat_succ cat_zero) C)) [P : τ (Functor (Product_cat C C) C)] (BP : τ
  (@BinaryProducts C P)) ⊢ (@counit_adj_transf C (Product_cat C C) (@product_diagonal_func C) P
  (@one_cat_binary_product_adjunction C C1 P BP)) ≡ (@Struct_sigma (@Transf (Product_cat C C) C (sigma_Fst
  (@comp_cat_fapp0 (Product_cat C C) C (Product_cat C C) (@product_diagonal_func C) P)) (@Product_projL_func C C)) (λ
  _ : τ (@Transf (Product_cat C C) C (sigma_Fst (@comp_cat_fapp0 (Product_cat C C) C (Product_cat C C)
  (@product_diagonal_func C) P)) (@Product_projL_func C C)), (@Transf (Product_cat C C) C (sigma_Snd (@comp_cat_fapp0
  (Product_cat C C) C (Product_cat C C) (@product_diagonal_func C) P)) (@Product_projR_func C C)))
  (@binary_products_proj1_transf C P BP) (@binary_products_proj2_transf C P BP));
assert [C : Cat] (C1 : τ (IsNCat (cat_succ cat_zero) C)) [P : τ (Functor (Product_cat C C) C)] (BP : τ
  (@BinaryProducts C P)) (a a' : τ (Obj (Product_cat C C))) (u : τ (Hom (Product_cat C C) a a'))
  ⊢ @tapp1_fapp0 (Product_cat C C) (Product_cat C C) (@comp_cat_fapp0 (Product_cat C C) C (Product_cat C C)
    (@product_diagonal_func C) P) (@id_func (Product_cat C C)) a a' (@counit_adj_transf C (Product_cat C C)
    (@product_diagonal_func C) P (@one_cat_binary_product_adjunction C C1 P BP)) u
    ≡ @tapp1_fapp0 (Product_cat C C) (Product_cat C C) (@comp_cat_fapp0 (Product_cat C C) C (Product_cat C C)
      (@product_diagonal_func C) P) (@id_func (Product_cat C C)) a a' (@Struct_sigma (@Transf (Product_cat C C) C
      (sigma_Fst (@comp_cat_fapp0 (Product_cat C C) C (Product_cat C C) (@product_diagonal_func C) P))
      (@Product_projL_func C C)) (λ _ : τ (@Transf (Product_cat C C) C (sigma_Fst (@comp_cat_fapp0 (Product_cat C C) C
      (Product_cat C C) (@product_diagonal_func C) P)) (@Product_projL_func C C)), (@Transf (Product_cat C C) C
      (sigma_Snd (@comp_cat_fapp0 (Product_cat C C) C (Product_cat C C) (@product_diagonal_func C) P))
      (@Product_projR_func C C))) (@binary_products_proj1_transf C P BP) (@binary_products_proj2_transf C P BP)) u;

// Both whole counit projections recover the original supplied projection transfors.
assert [C : Cat] (C1 : τ (IsNCat (cat_succ cat_zero) C)) [P : τ (Functor (Product_cat C C) C)] (BP : τ
  (@BinaryProducts C P)) ⊢ sigma_Fst (@counit_adj_transf C (Product_cat C C) (@product_diagonal_func C) P
  (@one_cat_binary_product_adjunction C C1 P BP)) ≡ @binary_products_proj1_transf C P BP;
assert [C : Cat] (C1 : τ (IsNCat (cat_succ cat_zero) C)) [P : τ (Functor (Product_cat C C) C)] (BP : τ
  (@BinaryProducts C P)) ⊢ sigma_Snd (@counit_adj_transf C (Product_cat C C) (@product_diagonal_func C) P
  (@one_cat_binary_product_adjunction C C1 P BP)) ≡ @binary_products_proj2_transf C P BP;
