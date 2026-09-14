require open emdash.emdash3_2_product_family_reindex;

// The raw L projection retains its original whole coordinate.
assert [B C D : Cat] (F : τ (Functor B C)) (G : τ (Functor B D)) ⊢ @eq_refl (Functor B C) (@comp_cat_fapp0 B
  (Product_cat C D) C (@Product_projL_func C D) (@Struct_sigma (Functor B C) (λ _ : τ (Functor B C), Functor B D)
  F G)) : τ (@= (Functor B C) (@comp_cat_fapp0 B (Product_cat C D) C (@Product_projL_func C D) (@Struct_sigma
  (Functor B C) (λ _ : τ (Functor B C), Functor B D) F G)) F);

// The native L projection retains its original whole coordinate.
assert [B C D : Cat] (F : τ (Functor B C)) (G : τ (Functor B D)) ⊢ @eq_refl (Functor B C) (@fapp0 (Functor_cat
  (Product_cat C D) C) (Functor_cat B C) (@comp_cat_con_func B (Product_cat C D) C (@Struct_sigma (Functor B C) (λ
  _ : τ (Functor B C), Functor B D) F G)) (@Product_projL_func C D)) : τ (@= (Functor B C) (@fapp0 (Functor_cat
  (Product_cat C D) C) (Functor_cat B C) (@comp_cat_con_func B (Product_cat C D) C (@Struct_sigma (Functor B C) (λ
  _ : τ (Functor B C), Functor B D) F G)) (@Product_projL_func C D)) F);

// The raw R projection retains its original whole coordinate.
assert [B C D : Cat] (F : τ (Functor B C)) (G : τ (Functor B D)) ⊢ @eq_refl (Functor B D) (@comp_cat_fapp0 B
  (Product_cat C D) D (@Product_projR_func C D) (@Struct_sigma (Functor B C) (λ _ : τ (Functor B C), Functor B D)
  F G)) : τ (@= (Functor B D) (@comp_cat_fapp0 B (Product_cat C D) D (@Product_projR_func C D) (@Struct_sigma
  (Functor B C) (λ _ : τ (Functor B C), Functor B D) F G)) G);

// The native R projection retains its original whole coordinate.
assert [B C D : Cat] (F : τ (Functor B C)) (G : τ (Functor B D)) ⊢ @eq_refl (Functor B D) (@fapp0 (Functor_cat
  (Product_cat C D) D) (Functor_cat B D) (@comp_cat_con_func B (Product_cat C D) D (@Struct_sigma (Functor B C) (λ
  _ : τ (Functor B C), Functor B D) F G)) (@Product_projR_func C D)) : τ (@= (Functor B D) (@fapp0 (Functor_cat
  (Product_cat C D) D) (Functor_cat B D) (@comp_cat_con_func B (Product_cat C D) D (@Struct_sigma (Functor B C) (λ
  _ : τ (Functor B C), Functor B D) F G)) (@Product_projR_func C D)) G);

// Identity-source Hom restriction retains both original coordinate actions for arbitrary F.
assert [A C : Cat] (X Y : τ (Functor A C)) (F : τ (Functor (Product_cat C C) C)) ⊢ @eq_refl (Functor (Hom_cat
  (Functor_cat (Product_cat C C) (Product_cat C C)) (@id_func (Product_cat C C)) (@comp_cat_fapp0 (Product_cat C
  C) C (Product_cat C C) (@product_diagonal_func C) F)) (Hom_cat (Functor_cat A (Product_cat C C))
  (@comp_cat_fapp0 A (Product_cat C C) (Product_cat C C) (@id_func (Product_cat C C)) (@Struct_sigma (Functor A C)
  (λ _ : τ (Functor A C), Functor A C) X Y)) (@comp_cat_fapp0 A (Product_cat C C) (Product_cat C C)
  (@comp_cat_fapp0 (Product_cat C C) C (Product_cat C C) (@product_diagonal_func C) F) (@Struct_sigma (Functor A
  C) (λ _ : τ (Functor A C), Functor A C) X Y)))) (@comp_cat_con_fapp1_func A (Product_cat C C) (Product_cat C C)
  (@Struct_sigma (Functor A C) (λ _ : τ (Functor A C), Functor A C) X Y) (@id_func (Product_cat C C))
  (@comp_cat_fapp0 (Product_cat C C) C (Product_cat C C) (@product_diagonal_func C) F)) : τ (@= (Functor (Hom_cat
  (Functor_cat (Product_cat C C) (Product_cat C C)) (@id_func (Product_cat C C)) (@comp_cat_fapp0 (Product_cat C
  C) C (Product_cat C C) (@product_diagonal_func C) F)) (Hom_cat (Functor_cat A (Product_cat C C))
  (@comp_cat_fapp0 A (Product_cat C C) (Product_cat C C) (@id_func (Product_cat C C)) (@Struct_sigma (Functor A C)
  (λ _ : τ (Functor A C), Functor A C) X Y)) (@comp_cat_fapp0 A (Product_cat C C) (Product_cat C C)
  (@comp_cat_fapp0 (Product_cat C C) C (Product_cat C C) (@product_diagonal_func C) F) (@Struct_sigma (Functor A
  C) (λ _ : τ (Functor A C), Functor A C) X Y)))) (@comp_cat_con_fapp1_func A (Product_cat C C) (Product_cat C C)
  (@Struct_sigma (Functor A C) (λ _ : τ (Functor A C), Functor A C) X Y) (@id_func (Product_cat C C))
  (@comp_cat_fapp0 (Product_cat C C) C (Product_cat C C) (@product_diagonal_func C) F)) (@Product_map_func
  (@Transf_cat (Product_cat C C) C (@Product_projL_func C C) F) (@Transf_cat A C (@comp_cat_fapp0 A (Product_cat C
  C) C (@Product_projL_func C C) (@Struct_sigma (Functor A C) (λ _ : τ (Functor A C), Functor A C) X Y))
  (@comp_cat_fapp0 A (Product_cat C C) C F (@Struct_sigma (Functor A C) (λ _ : τ (Functor A C), Functor A C) X
  Y))) (@Transf_cat (Product_cat C C) C (@Product_projR_func C C) F) (@Transf_cat A C (@comp_cat_fapp0 A
  (Product_cat C C) C (@Product_projR_func C C) (@Struct_sigma (Functor A C) (λ _ : τ (Functor A C), Functor A C)
  X Y)) (@comp_cat_fapp0 A (Product_cat C C) C F (@Struct_sigma (Functor A C) (λ _ : τ (Functor A C), Functor A C)
  X Y))) (@comp_cat_con_fapp1_func A (Product_cat C C) C (@Struct_sigma (Functor A C) (λ _ : τ (Functor A C),
  Functor A C) X Y) (@Product_projL_func C C) F) (@comp_cat_con_fapp1_func A (Product_cat C C) C (@Struct_sigma
  (Functor A C) (λ _ : τ (Functor A C), Functor A C) X Y) (@Product_projR_func C C) F)));

// Identity-target Hom restriction retains both original coordinate actions for arbitrary F.
assert [A C : Cat] (X Y : τ (Functor A C)) (F : τ (Functor (Product_cat C C) C)) ⊢ @eq_refl (Functor (Hom_cat
  (Functor_cat (Product_cat C C) (Product_cat C C)) (@comp_cat_fapp0 (Product_cat C C) C (Product_cat C C)
  (@product_diagonal_func C) F) (@id_func (Product_cat C C))) (Hom_cat (Functor_cat A (Product_cat C C))
  (@comp_cat_fapp0 A (Product_cat C C) (Product_cat C C) (@comp_cat_fapp0 (Product_cat C C) C (Product_cat C C)
  (@product_diagonal_func C) F) (@Struct_sigma (Functor A C) (λ _ : τ (Functor A C), Functor A C) X Y))
  (@comp_cat_fapp0 A (Product_cat C C) (Product_cat C C) (@id_func (Product_cat C C)) (@Struct_sigma (Functor A C)
  (λ _ : τ (Functor A C), Functor A C) X Y)))) (@comp_cat_con_fapp1_func A (Product_cat C C) (Product_cat C C)
  (@Struct_sigma (Functor A C) (λ _ : τ (Functor A C), Functor A C) X Y) (@comp_cat_fapp0 (Product_cat C C) C
  (Product_cat C C) (@product_diagonal_func C) F) (@id_func (Product_cat C C))) : τ (@= (Functor (Hom_cat
  (Functor_cat (Product_cat C C) (Product_cat C C)) (@comp_cat_fapp0 (Product_cat C C) C (Product_cat C C)
  (@product_diagonal_func C) F) (@id_func (Product_cat C C))) (Hom_cat (Functor_cat A (Product_cat C C))
  (@comp_cat_fapp0 A (Product_cat C C) (Product_cat C C) (@comp_cat_fapp0 (Product_cat C C) C (Product_cat C C)
  (@product_diagonal_func C) F) (@Struct_sigma (Functor A C) (λ _ : τ (Functor A C), Functor A C) X Y))
  (@comp_cat_fapp0 A (Product_cat C C) (Product_cat C C) (@id_func (Product_cat C C)) (@Struct_sigma (Functor A C)
  (λ _ : τ (Functor A C), Functor A C) X Y)))) (@comp_cat_con_fapp1_func A (Product_cat C C) (Product_cat C C)
  (@Struct_sigma (Functor A C) (λ _ : τ (Functor A C), Functor A C) X Y) (@comp_cat_fapp0 (Product_cat C C) C
  (Product_cat C C) (@product_diagonal_func C) F) (@id_func (Product_cat C C))) (@Product_map_func (@Transf_cat
  (Product_cat C C) C F (@Product_projL_func C C)) (@Transf_cat A C (@comp_cat_fapp0 A (Product_cat C C) C F
  (@Struct_sigma (Functor A C) (λ _ : τ (Functor A C), Functor A C) X Y)) (@comp_cat_fapp0 A (Product_cat C C) C
  (@Product_projL_func C C) (@Struct_sigma (Functor A C) (λ _ : τ (Functor A C), Functor A C) X Y))) (@Transf_cat
  (Product_cat C C) C F (@Product_projR_func C C)) (@Transf_cat A C (@comp_cat_fapp0 A (Product_cat C C) C F
  (@Struct_sigma (Functor A C) (λ _ : τ (Functor A C), Functor A C) X Y)) (@comp_cat_fapp0 A (Product_cat C C) C
  (@Product_projR_func C C) (@Struct_sigma (Functor A C) (λ _ : τ (Functor A C), Functor A C) X Y)))
  (@comp_cat_con_fapp1_func A (Product_cat C C) C (@Struct_sigma (Functor A C) (λ _ : τ (Functor A C), Functor A
  C) X Y) F (@Product_projL_func C C)) (@comp_cat_con_fapp1_func A (Product_cat C C) C (@Struct_sigma (Functor A
  C) (λ _ : τ (Functor A C), Functor A C) X Y) F (@Product_projR_func C C))));

// A first projection cannot select an unrelated whole functor.
assertnot [B C D : Cat] (F : τ (Functor B C)) (G : τ (Functor B D)) (other : τ (Functor B C))
 ⊢ @eq_refl (Functor B C) F : τ (@= (Functor B C)
 (@comp_cat_fapp0 B (Product_cat C D) C (@Product_projL_func C D)
 (@Struct_sigma (Functor B C) (λ _ : τ (Functor B C), Functor B D) F G)) other);
