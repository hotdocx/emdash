/* Whole diagonal action, native parameter views, and noncollapse controls. */
require open emdash.emdash3_2_product_family_action_views;

assert [B C : Cat] (X Y : τ (Functor B C)) ⊢ @eq_refl (Functor (@Transf_cat B C X Y) (Hom_cat (Functor_cat B
  (Product_cat C C)) (@fapp0 (Functor_cat B C) (Functor_cat B (Product_cat C C)) (@comp_cat_cov_func B C (Product_cat
  C C) (@product_diagonal_func C)) X) (@fapp0 (Functor_cat B C) (Functor_cat B (Product_cat C C)) (@comp_cat_cov_func
  B C (Product_cat C C) (@product_diagonal_func C)) Y))) (@fapp1_func (Functor_cat B C) (Functor_cat B (Product_cat C
  C)) (@comp_cat_cov_func B C (Product_cat C C) (@product_diagonal_func C)) X Y)
  : τ (@= (Functor (@Transf_cat B C X Y) (Hom_cat (Functor_cat B (Product_cat C C)) (@fapp0 (Functor_cat B C)
  (Functor_cat B (Product_cat C C)) (@comp_cat_cov_func B C (Product_cat C C) (@product_diagonal_func C)) X) (@fapp0
  (Functor_cat B C) (Functor_cat B (Product_cat C C)) (@comp_cat_cov_func B C (Product_cat C C)
  (@product_diagonal_func C)) Y))) (@fapp1_func (Functor_cat B C) (Functor_cat B (Product_cat C C))
  (@comp_cat_cov_func B C (Product_cat C C) (@product_diagonal_func C)) X Y) (@product_diagonal_func (@Transf_cat B C
  X Y)));
assert [B C : Cat] (X Y : τ (Functor B C)) (h : τ (@Transf B C X Y)) ⊢ @diagonal_family_native_proj1_path B C X Y h :
  τ (@= (@Transf B C X Y) (@sigma_Fst (Obj (Hom_cat (Functor_cat B C) (@sigma_Fst (Obj (Functor_cat B C)) (λ _ : τ
  (Obj (Functor_cat B C)), Obj (Functor_cat B C)) (@fapp0 (Functor_cat B C) (Functor_cat B (Product_cat C C))
  (@comp_cat_cov_func B C (Product_cat C C) (@product_diagonal_func C)) X)) (@sigma_Fst (Obj (Functor_cat B C)) (λ _ :
  τ (Obj (Functor_cat B C)), Obj (Functor_cat B C)) (@fapp0 (Functor_cat B C) (Functor_cat B (Product_cat C C))
  (@comp_cat_cov_func B C (Product_cat C C) (@product_diagonal_func C)) Y)))) (λ _ : τ (Obj (Hom_cat (Functor_cat B C)
  (@sigma_Fst (Obj (Functor_cat B C)) (λ _ : τ (Obj (Functor_cat B C)), Obj (Functor_cat B C)) (@fapp0 (Functor_cat B
  C) (Functor_cat B (Product_cat C C)) (@comp_cat_cov_func B C (Product_cat C C) (@product_diagonal_func C)) X))
  (@sigma_Fst (Obj (Functor_cat B C)) (λ _ : τ (Obj (Functor_cat B C)), Obj (Functor_cat B C)) (@fapp0 (Functor_cat B
  C) (Functor_cat B (Product_cat C C)) (@comp_cat_cov_func B C (Product_cat C C) (@product_diagonal_func C)) Y)))),
  (Obj (Hom_cat (Functor_cat B C) (@sigma_Snd (Obj (Functor_cat B C)) (λ _ : τ (Obj (Functor_cat B C)), Obj
  (Functor_cat B C)) (@fapp0 (Functor_cat B C) (Functor_cat B (Product_cat C C)) (@comp_cat_cov_func B C (Product_cat
  C C) (@product_diagonal_func C)) X)) (@sigma_Snd (Obj (Functor_cat B C)) (λ _ : τ (Obj (Functor_cat B C)), Obj
  (Functor_cat B C)) (@fapp0 (Functor_cat B C) (Functor_cat B (Product_cat C C)) (@comp_cat_cov_func B C (Product_cat
  C C) (@product_diagonal_func C)) Y))))) (@fapp1_fapp0 (Functor_cat B C) (Functor_cat B (Product_cat C C))
  (@comp_cat_cov_func B C (Product_cat C C) (@product_diagonal_func C)) X Y h)) h);
assert [B C : Cat] (X Y : τ (Functor B C)) (h : τ (@Transf B C X Y)) ⊢ @diagonal_family_native_proj2_path B C X Y h :
  τ (@= (@Transf B C X Y) (@sigma_Snd (Obj (Hom_cat (Functor_cat B C) (@sigma_Fst (Obj (Functor_cat B C)) (λ _ : τ
  (Obj (Functor_cat B C)), Obj (Functor_cat B C)) (@fapp0 (Functor_cat B C) (Functor_cat B (Product_cat C C))
  (@comp_cat_cov_func B C (Product_cat C C) (@product_diagonal_func C)) X)) (@sigma_Fst (Obj (Functor_cat B C)) (λ _ :
  τ (Obj (Functor_cat B C)), Obj (Functor_cat B C)) (@fapp0 (Functor_cat B C) (Functor_cat B (Product_cat C C))
  (@comp_cat_cov_func B C (Product_cat C C) (@product_diagonal_func C)) Y)))) (λ _ : τ (Obj (Hom_cat (Functor_cat B C)
  (@sigma_Fst (Obj (Functor_cat B C)) (λ _ : τ (Obj (Functor_cat B C)), Obj (Functor_cat B C)) (@fapp0 (Functor_cat B
  C) (Functor_cat B (Product_cat C C)) (@comp_cat_cov_func B C (Product_cat C C) (@product_diagonal_func C)) X))
  (@sigma_Fst (Obj (Functor_cat B C)) (λ _ : τ (Obj (Functor_cat B C)), Obj (Functor_cat B C)) (@fapp0 (Functor_cat B
  C) (Functor_cat B (Product_cat C C)) (@comp_cat_cov_func B C (Product_cat C C) (@product_diagonal_func C)) Y)))),
  (Obj (Hom_cat (Functor_cat B C) (@sigma_Snd (Obj (Functor_cat B C)) (λ _ : τ (Obj (Functor_cat B C)), Obj
  (Functor_cat B C)) (@fapp0 (Functor_cat B C) (Functor_cat B (Product_cat C C)) (@comp_cat_cov_func B C (Product_cat
  C C) (@product_diagonal_func C)) X)) (@sigma_Snd (Obj (Functor_cat B C)) (λ _ : τ (Obj (Functor_cat B C)), Obj
  (Functor_cat B C)) (@fapp0 (Functor_cat B C) (Functor_cat B (Product_cat C C)) (@comp_cat_cov_func B C (Product_cat
  C C) (@product_diagonal_func C)) Y))))) (@fapp1_fapp0 (Functor_cat B C) (Functor_cat B (Product_cat C C))
  (@comp_cat_cov_func B C (Product_cat C C) (@product_diagonal_func C)) X Y h)) h);
assert [B C : Cat] (X Y : τ (Functor B C)) (h : τ (@Transf B C X Y)) (i j : τ (Obj B)) (p : τ (Hom B i j)) ⊢ @eq_ap
  (@Transf B C X Y) (Hom C (@fapp0 B C X i) (@fapp0 B C Y j)) (λ k : τ (@Transf B C X Y), @tapp1_fapp0 B C X Y i j k
  p) (@sigma_Fst (Obj (Hom_cat (Functor_cat B C) (@sigma_Fst (Obj (Functor_cat B C)) (λ _ : τ (Obj (Functor_cat B C)),
  Obj (Functor_cat B C)) (@fapp0 (Functor_cat B C) (Functor_cat B (Product_cat C C)) (@comp_cat_cov_func B C
  (Product_cat C C) (@product_diagonal_func C)) X)) (@sigma_Fst (Obj (Functor_cat B C)) (λ _ : τ (Obj (Functor_cat B
  C)), Obj (Functor_cat B C)) (@fapp0 (Functor_cat B C) (Functor_cat B (Product_cat C C)) (@comp_cat_cov_func B C
  (Product_cat C C) (@product_diagonal_func C)) Y)))) (λ _ : τ (Obj (Hom_cat (Functor_cat B C) (@sigma_Fst (Obj
  (Functor_cat B C)) (λ _ : τ (Obj (Functor_cat B C)), Obj (Functor_cat B C)) (@fapp0 (Functor_cat B C) (Functor_cat B
  (Product_cat C C)) (@comp_cat_cov_func B C (Product_cat C C) (@product_diagonal_func C)) X)) (@sigma_Fst (Obj
  (Functor_cat B C)) (λ _ : τ (Obj (Functor_cat B C)), Obj (Functor_cat B C)) (@fapp0 (Functor_cat B C) (Functor_cat B
  (Product_cat C C)) (@comp_cat_cov_func B C (Product_cat C C) (@product_diagonal_func C)) Y)))), (Obj (Hom_cat
  (Functor_cat B C) (@sigma_Snd (Obj (Functor_cat B C)) (λ _ : τ (Obj (Functor_cat B C)), Obj (Functor_cat B C))
  (@fapp0 (Functor_cat B C) (Functor_cat B (Product_cat C C)) (@comp_cat_cov_func B C (Product_cat C C)
  (@product_diagonal_func C)) X)) (@sigma_Snd (Obj (Functor_cat B C)) (λ _ : τ (Obj (Functor_cat B C)), Obj
  (Functor_cat B C)) (@fapp0 (Functor_cat B C) (Functor_cat B (Product_cat C C)) (@comp_cat_cov_func B C (Product_cat
  C C) (@product_diagonal_func C)) Y))))) (@fapp1_fapp0 (Functor_cat B C) (Functor_cat B (Product_cat C C))
  (@comp_cat_cov_func B C (Product_cat C C) (@product_diagonal_func C)) X Y h)) h (@diagonal_family_native_proj1_path
  B C X Y h) : τ (@= (Hom C (@fapp0 B C X i) (@fapp0 B C Y j)) (@tapp1_fapp0 B C X Y i j (@sigma_Fst (Obj (Hom_cat
  (Functor_cat B C) (@sigma_Fst (Obj (Functor_cat B C)) (λ _ : τ (Obj (Functor_cat B C)), Obj (Functor_cat B C))
  (@fapp0 (Functor_cat B C) (Functor_cat B (Product_cat C C)) (@comp_cat_cov_func B C (Product_cat C C)
  (@product_diagonal_func C)) X)) (@sigma_Fst (Obj (Functor_cat B C)) (λ _ : τ (Obj (Functor_cat B C)), Obj
  (Functor_cat B C)) (@fapp0 (Functor_cat B C) (Functor_cat B (Product_cat C C)) (@comp_cat_cov_func B C (Product_cat
  C C) (@product_diagonal_func C)) Y)))) (λ _ : τ (Obj (Hom_cat (Functor_cat B C) (@sigma_Fst (Obj (Functor_cat B C))
  (λ _ : τ (Obj (Functor_cat B C)), Obj (Functor_cat B C)) (@fapp0 (Functor_cat B C) (Functor_cat B (Product_cat C C))
  (@comp_cat_cov_func B C (Product_cat C C) (@product_diagonal_func C)) X)) (@sigma_Fst (Obj (Functor_cat B C)) (λ _ :
  τ (Obj (Functor_cat B C)), Obj (Functor_cat B C)) (@fapp0 (Functor_cat B C) (Functor_cat B (Product_cat C C))
  (@comp_cat_cov_func B C (Product_cat C C) (@product_diagonal_func C)) Y)))), (Obj (Hom_cat (Functor_cat B C)
  (@sigma_Snd (Obj (Functor_cat B C)) (λ _ : τ (Obj (Functor_cat B C)), Obj (Functor_cat B C)) (@fapp0 (Functor_cat B
  C) (Functor_cat B (Product_cat C C)) (@comp_cat_cov_func B C (Product_cat C C) (@product_diagonal_func C)) X))
  (@sigma_Snd (Obj (Functor_cat B C)) (λ _ : τ (Obj (Functor_cat B C)), Obj (Functor_cat B C)) (@fapp0 (Functor_cat B
  C) (Functor_cat B (Product_cat C C)) (@comp_cat_cov_func B C (Product_cat C C) (@product_diagonal_func C)) Y)))))
  (@fapp1_fapp0 (Functor_cat B C) (Functor_cat B (Product_cat C C)) (@comp_cat_cov_func B C (Product_cat C C)
  (@product_diagonal_func C)) X Y h)) p) (@tapp1_fapp0 B C X Y i j h p));
assert [B C : Cat] (X Y : τ (Functor B C)) (h : τ (@Transf B C X Y)) (i j : τ (Obj B))  ⊢ @eq_ap (@Transf B C X Y)
  (Functor (Hom_cat B i j) (Hom_cat C (@fapp0 B C X i) (@fapp0 B C Y j))) (λ k : τ (@Transf B C X Y), @tapp1_func B C
  X Y i j k) (@sigma_Fst (Obj (Hom_cat (Functor_cat B C) (@sigma_Fst (Obj (Functor_cat B C)) (λ _ : τ (Obj
  (Functor_cat B C)), Obj (Functor_cat B C)) (@fapp0 (Functor_cat B C) (Functor_cat B (Product_cat C C))
  (@comp_cat_cov_func B C (Product_cat C C) (@product_diagonal_func C)) X)) (@sigma_Fst (Obj (Functor_cat B C)) (λ _ :
  τ (Obj (Functor_cat B C)), Obj (Functor_cat B C)) (@fapp0 (Functor_cat B C) (Functor_cat B (Product_cat C C))
  (@comp_cat_cov_func B C (Product_cat C C) (@product_diagonal_func C)) Y)))) (λ _ : τ (Obj (Hom_cat (Functor_cat B C)
  (@sigma_Fst (Obj (Functor_cat B C)) (λ _ : τ (Obj (Functor_cat B C)), Obj (Functor_cat B C)) (@fapp0 (Functor_cat B
  C) (Functor_cat B (Product_cat C C)) (@comp_cat_cov_func B C (Product_cat C C) (@product_diagonal_func C)) X))
  (@sigma_Fst (Obj (Functor_cat B C)) (λ _ : τ (Obj (Functor_cat B C)), Obj (Functor_cat B C)) (@fapp0 (Functor_cat B
  C) (Functor_cat B (Product_cat C C)) (@comp_cat_cov_func B C (Product_cat C C) (@product_diagonal_func C)) Y)))),
  (Obj (Hom_cat (Functor_cat B C) (@sigma_Snd (Obj (Functor_cat B C)) (λ _ : τ (Obj (Functor_cat B C)), Obj
  (Functor_cat B C)) (@fapp0 (Functor_cat B C) (Functor_cat B (Product_cat C C)) (@comp_cat_cov_func B C (Product_cat
  C C) (@product_diagonal_func C)) X)) (@sigma_Snd (Obj (Functor_cat B C)) (λ _ : τ (Obj (Functor_cat B C)), Obj
  (Functor_cat B C)) (@fapp0 (Functor_cat B C) (Functor_cat B (Product_cat C C)) (@comp_cat_cov_func B C (Product_cat
  C C) (@product_diagonal_func C)) Y))))) (@fapp1_fapp0 (Functor_cat B C) (Functor_cat B (Product_cat C C))
  (@comp_cat_cov_func B C (Product_cat C C) (@product_diagonal_func C)) X Y h)) h (@diagonal_family_native_proj1_path
  B C X Y h) : τ (@= (Functor (Hom_cat B i j) (Hom_cat C (@fapp0 B C X i) (@fapp0 B C Y j))) (@tapp1_func B C X Y i j
  (@sigma_Fst (Obj (Hom_cat (Functor_cat B C) (@sigma_Fst (Obj (Functor_cat B C)) (λ _ : τ (Obj (Functor_cat B C)),
  Obj (Functor_cat B C)) (@fapp0 (Functor_cat B C) (Functor_cat B (Product_cat C C)) (@comp_cat_cov_func B C
  (Product_cat C C) (@product_diagonal_func C)) X)) (@sigma_Fst (Obj (Functor_cat B C)) (λ _ : τ (Obj (Functor_cat B
  C)), Obj (Functor_cat B C)) (@fapp0 (Functor_cat B C) (Functor_cat B (Product_cat C C)) (@comp_cat_cov_func B C
  (Product_cat C C) (@product_diagonal_func C)) Y)))) (λ _ : τ (Obj (Hom_cat (Functor_cat B C) (@sigma_Fst (Obj
  (Functor_cat B C)) (λ _ : τ (Obj (Functor_cat B C)), Obj (Functor_cat B C)) (@fapp0 (Functor_cat B C) (Functor_cat B
  (Product_cat C C)) (@comp_cat_cov_func B C (Product_cat C C) (@product_diagonal_func C)) X)) (@sigma_Fst (Obj
  (Functor_cat B C)) (λ _ : τ (Obj (Functor_cat B C)), Obj (Functor_cat B C)) (@fapp0 (Functor_cat B C) (Functor_cat B
  (Product_cat C C)) (@comp_cat_cov_func B C (Product_cat C C) (@product_diagonal_func C)) Y)))), (Obj (Hom_cat
  (Functor_cat B C) (@sigma_Snd (Obj (Functor_cat B C)) (λ _ : τ (Obj (Functor_cat B C)), Obj (Functor_cat B C))
  (@fapp0 (Functor_cat B C) (Functor_cat B (Product_cat C C)) (@comp_cat_cov_func B C (Product_cat C C)
  (@product_diagonal_func C)) X)) (@sigma_Snd (Obj (Functor_cat B C)) (λ _ : τ (Obj (Functor_cat B C)), Obj
  (Functor_cat B C)) (@fapp0 (Functor_cat B C) (Functor_cat B (Product_cat C C)) (@comp_cat_cov_func B C (Product_cat
  C C) (@product_diagonal_func C)) Y))))) (@fapp1_fapp0 (Functor_cat B C) (Functor_cat B (Product_cat C C))
  (@comp_cat_cov_func B C (Product_cat C C) (@product_diagonal_func C)) X Y h))) (@tapp1_func B C X Y i j h));
assertnot [B C : Cat] (X Y : τ (Functor B C)) (K : τ (Functor (@Transf_cat B C X Y) (@Transf_cat B C X Y))) ⊢ @eq_refl
  (Functor (@Transf_cat B C X Y) (Hom_cat (Functor_cat B (Product_cat C C)) (@fapp0 (Functor_cat B C) (Functor_cat B
  (Product_cat C C)) (@comp_cat_cov_func B C (Product_cat C C) (@product_diagonal_func C)) X) (@fapp0 (Functor_cat B
  C) (Functor_cat B (Product_cat C C)) (@comp_cat_cov_func B C (Product_cat C C) (@product_diagonal_func C)) Y)))
  (@fapp1_func (Functor_cat B C) (Functor_cat B (Product_cat C C)) (@comp_cat_cov_func B C (Product_cat C C)
  (@product_diagonal_func C)) X Y) : τ (@= (Functor (@Transf_cat B C X Y) (Hom_cat (Functor_cat B (Product_cat C C))
  (@fapp0 (Functor_cat B C) (Functor_cat B (Product_cat C C)) (@comp_cat_cov_func B C (Product_cat C C)
  (@product_diagonal_func C)) X) (@fapp0 (Functor_cat B C) (Functor_cat B (Product_cat C C)) (@comp_cat_cov_func B C
  (Product_cat C C) (@product_diagonal_func C)) Y))) (@fapp1_func (Functor_cat B C) (Functor_cat B (Product_cat C C))
  (@comp_cat_cov_func B C (Product_cat C C) (@product_diagonal_func C)) X Y) (@Struct_sigma (Functor (@Transf_cat B C
  X Y) (@Transf_cat B C X Y)) (λ _ : τ (Functor (@Transf_cat B C X Y) (@Transf_cat B C X Y)), Functor (@Transf_cat B C
  X Y) (@Transf_cat B C X Y)) (@id_func (@Transf_cat B C X Y)) K));
assert [A B C D : Cat] (F : τ (Functor B A)) (H : τ (Functor A (Product_cat C D))) ⊢ @eq_refl (Functor B C) (sigma_Fst
  (@hom_postcomp_fapp0 Cat_cat Cat_cat (@id_func Cat_cat) B A (Product_cat C D) H F)) : τ (@= (Functor B C) (sigma_Fst
  (@hom_postcomp_fapp0 Cat_cat Cat_cat (@id_func Cat_cat) B A (Product_cat C D) H F)) (@hom_postcomp_fapp0 Cat_cat
  Cat_cat (@id_func Cat_cat) B A C (sigma_Fst H) F));
assertnot [A B C D : Cat] (F F0 : τ (Functor B A)) (H : τ (Functor A (Product_cat C D))) ⊢ @eq_refl (Functor B C)
  (sigma_Fst (@hom_postcomp_fapp0 Cat_cat Cat_cat (@id_func Cat_cat) B A (Product_cat C D) H F)) : τ (@= (Functor B C)
  (sigma_Fst (@hom_postcomp_fapp0 Cat_cat Cat_cat (@id_func Cat_cat) B A (Product_cat C D) H F)) (@hom_postcomp_fapp0
  Cat_cat Cat_cat (@id_func Cat_cat) B A C (sigma_Fst H) F0));
assert [A B C D : Cat] (F : τ (Functor B A)) (H : τ (Functor A (Product_cat C D))) ⊢ @eq_refl (Functor B D) (sigma_Snd
  (@hom_postcomp_fapp0 Cat_cat Cat_cat (@id_func Cat_cat) B A (Product_cat C D) H F)) : τ (@= (Functor B D) (sigma_Snd
  (@hom_postcomp_fapp0 Cat_cat Cat_cat (@id_func Cat_cat) B A (Product_cat C D) H F)) (@hom_postcomp_fapp0 Cat_cat
  Cat_cat (@id_func Cat_cat) B A D (sigma_Snd H) F));
assertnot [A B C D : Cat] (F F0 : τ (Functor B A)) (H : τ (Functor A (Product_cat C D))) ⊢ @eq_refl (Functor B D)
  (sigma_Snd (@hom_postcomp_fapp0 Cat_cat Cat_cat (@id_func Cat_cat) B A (Product_cat C D) H F)) : τ (@= (Functor B D)
  (sigma_Snd (@hom_postcomp_fapp0 Cat_cat Cat_cat (@id_func Cat_cat) B A (Product_cat C D) H F)) (@hom_postcomp_fapp0
  Cat_cat Cat_cat (@id_func Cat_cat) B A D (sigma_Snd H) F0));
assert [B C : Cat] (X Y : τ (Functor B C)) (h : τ (@Transf B C X Y)) ⊢ @eq_refl (@Transf B C X Y) h : τ (@= (@Transf B
  C X Y) (@fapp0 (@Transf_cat B C X Y) (Hom_cat (Functor_cat B C) (@sigma_Fst (Obj (Functor_cat B C)) (λ _ : τ (Obj
  (Functor_cat B C)), Obj (Functor_cat B C)) (@fapp0 (Functor_cat B C) (Functor_cat B (Product_cat C C))
  (@comp_cat_cov_func B C (Product_cat C C) (@product_diagonal_func C)) X)) (@sigma_Fst (Obj (Functor_cat B C)) (λ _ :
  τ (Obj (Functor_cat B C)), Obj (Functor_cat B C)) (@fapp0 (Functor_cat B C) (Functor_cat B (Product_cat C C))
  (@comp_cat_cov_func B C (Product_cat C C) (@product_diagonal_func C)) Y))) (@id_func (@Transf_cat B C X Y)) h) h);
assertnot [B C : Cat] (X Y : τ (Functor B C)) (h k : τ (@Transf B C X Y)) ⊢ @eq_refl (@Transf B C X Y) h : τ (@=
  (@Transf B C X Y) (@fapp0 (@Transf_cat B C X Y) (Hom_cat (Functor_cat B C) (@sigma_Fst (Obj (Functor_cat B C)) (λ _
  : τ (Obj (Functor_cat B C)), Obj (Functor_cat B C)) (@fapp0 (Functor_cat B C) (Functor_cat B (Product_cat C C))
  (@comp_cat_cov_func B C (Product_cat C C) (@product_diagonal_func C)) X)) (@sigma_Fst (Obj (Functor_cat B C)) (λ _ :
  τ (Obj (Functor_cat B C)), Obj (Functor_cat B C)) (@fapp0 (Functor_cat B C) (Functor_cat B (Product_cat C C))
  (@comp_cat_cov_func B C (Product_cat C C) (@product_diagonal_func C)) Y))) (@id_func (@Transf_cat B C X Y)) h) k);
assert [B C : Cat] (X Y Z : τ (Functor B C)) (f : τ (@Transf B C X Y)) (g : τ (@Transf B C Y Z)) ⊢ @eq_refl (@Transf B
  C X Z) (@comp_fapp0 (Functor_cat B C) X Y Z g f) : τ (@= (@Transf B C X Z) (@comp_fapp0 (Functor_cat B C)
  (@sigma_Fst (Obj (Functor_cat B C)) (λ _ : τ (Obj (Functor_cat B C)), Obj (Functor_cat B C)) (@fapp0 (Functor_cat B
  C) (Functor_cat B (Product_cat C C)) (@comp_cat_cov_func B C (Product_cat C C) (@product_diagonal_func C)) X))
  (@sigma_Fst (Obj (Functor_cat B C)) (λ _ : τ (Obj (Functor_cat B C)), Obj (Functor_cat B C)) (@fapp0 (Functor_cat B
  C) (Functor_cat B (Product_cat C C)) (@comp_cat_cov_func B C (Product_cat C C) (@product_diagonal_func C)) Y))
  (@sigma_Fst (Obj (Functor_cat B C)) (λ _ : τ (Obj (Functor_cat B C)), Obj (Functor_cat B C)) (@fapp0 (Functor_cat B
  C) (Functor_cat B (Product_cat C C)) (@comp_cat_cov_func B C (Product_cat C C) (@product_diagonal_func C)) Z)) g f)
  (@comp_fapp0 (Functor_cat B C) X Y Z g f));
assertnot [B C : Cat] (X Y Z : τ (Functor B C)) (f f0 : τ (@Transf B C X Y)) (g : τ (@Transf B C Y Z)) ⊢ @eq_refl
  (@Transf B C X Z) (@comp_fapp0 (Functor_cat B C) X Y Z g f) : τ (@= (@Transf B C X Z) (@comp_fapp0 (Functor_cat B C)
  (@sigma_Fst (Obj (Functor_cat B C)) (λ _ : τ (Obj (Functor_cat B C)), Obj (Functor_cat B C)) (@fapp0 (Functor_cat B
  C) (Functor_cat B (Product_cat C C)) (@comp_cat_cov_func B C (Product_cat C C) (@product_diagonal_func C)) X))
  (@sigma_Fst (Obj (Functor_cat B C)) (λ _ : τ (Obj (Functor_cat B C)), Obj (Functor_cat B C)) (@fapp0 (Functor_cat B
  C) (Functor_cat B (Product_cat C C)) (@comp_cat_cov_func B C (Product_cat C C) (@product_diagonal_func C)) Y))
  (@sigma_Fst (Obj (Functor_cat B C)) (λ _ : τ (Obj (Functor_cat B C)), Obj (Functor_cat B C)) (@fapp0 (Functor_cat B
  C) (Functor_cat B (Product_cat C C)) (@comp_cat_cov_func B C (Product_cat C C) (@product_diagonal_func C)) Z)) g f)
  (@comp_fapp0 (Functor_cat B C) X Y Z g f0));
assert [B C : Cat] (W X Y Z : τ (Functor B C)) (f : τ (@Transf B C W X)) (g : τ (@Transf B C X Y)) (h : τ (@Transf B C
  Y Z)) ⊢ @comp_assoc (Functor_cat B C) W X Y Z h g f : τ (@= (@Transf B C W Z) (@comp_fapp0 (Functor_cat B C) W Y Z h
  (@comp_fapp0 (Functor_cat B C) W X Y g f)) (@comp_fapp0 (Functor_cat B C) W X Z (@comp_fapp0 (Functor_cat B C) X Y Z
  h g) f));
