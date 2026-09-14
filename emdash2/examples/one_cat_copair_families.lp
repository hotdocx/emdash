/* Native copairing inverse cuts and retained action. */
require open emdash.emdash3_2_one_cat_copair_family_paths;

assert [B C : Cat] (C1 : τ (IsNCat (cat_succ cat_zero) C))
  [Prod : τ (Functor (Product_cat C C) C)] [t : τ (Obj C)]
  (A : τ (@AdditiveCategory C Prod t)) (T0 : τ (@TerminalObject (Op_cat C) t)) (X Y Z : τ (Functor B C)) (f : τ
  (@Transf B C X Z)) (g : τ (@Transf B C Y Z)) ⊢ (@one_cat_uncopair_family B C C1 Prod t A T0 X Y Z
  (@one_cat_copair_family B C C1 Prod t A T0 X Y Z f g)) ≡ (@Struct_sigma (@Transf B C X Z) (λ _ : τ (@Transf B
  C X Z), @Transf B C Y Z) f g);
assert [B C : Cat] (C1 : τ (IsNCat (cat_succ cat_zero) C))
  [Prod : τ (Functor (Product_cat C C) C)] [t : τ (Obj C)]
  (A : τ (@AdditiveCategory C Prod t)) (T0 : τ (@TerminalObject (Op_cat C) t)) (X Y Z : τ (Functor B C)) (h : τ (Obj
  (@Transf_cat B C (@fapp0 (Functor_cat B (Product_cat C C)) (Functor_cat B C) (@comp_cat_cov_func B (Product_cat C C)
  C Prod) (@Struct_sigma (Functor B C) (λ _ : τ (Functor B C), Functor B C) X Y)) Z))) ⊢ @fapp0 (Hom_cat (Functor_cat
  B (Product_cat C C)) (@Struct_sigma (Functor B C) (λ _ : τ (Functor B C), Functor B C) X Y) (@fapp0 (Functor_cat B
  C) (Functor_cat B (Product_cat C C)) (@comp_cat_cov_func B C (Product_cat C C) (@product_diagonal_func C)) Z))
  (@Transf_cat B C (@fapp0 (Functor_cat B (Product_cat C C)) (Functor_cat B C) (@comp_cat_cov_func B (Product_cat C C)
  C Prod) (@Struct_sigma (Functor B C) (λ _ : τ (Functor B C), Functor B C) X Y)) Z)
  (@one_cat_copair_family_func B C C1 Prod t A T0 X Y Z) (@one_cat_uncopair_family B C C1 Prod t A T0 X Y
  Z h) ≡ h;

assert [B C : Cat] (C1 : τ (IsNCat (cat_succ cat_zero) C))
  [Prod : τ (Functor (Product_cat C C) C)] [t : τ (Obj C)]
  (A : τ (@AdditiveCategory C Prod t)) (T0 : τ (@TerminalObject (Op_cat C) t)) (X Y Z : τ (Functor B C)) ⊢
  (@comp_cat_fapp0 (Hom_cat (Functor_cat B (Product_cat C C)) (@Struct_sigma (Functor B C) (λ _ : τ (Functor B C),
  Functor B C) X Y) (@fapp0 (Functor_cat B C) (Functor_cat B (Product_cat C C)) (@comp_cat_cov_func B C (Product_cat C
  C) (@product_diagonal_func C)) Z)) (@Transf_cat B C (@fapp0 (Functor_cat B (Product_cat C C)) (Functor_cat B C)
  (@comp_cat_cov_func B (Product_cat C C) C Prod) (@Struct_sigma (Functor B C) (λ _ : τ (Functor B C), Functor B C) X
  Y)) Z) (Hom_cat (Functor_cat B (Product_cat C C)) (@Struct_sigma (Functor B C) (λ _ : τ (Functor B C), Functor B C)
  X Y) (@fapp0 (Functor_cat B C) (Functor_cat B (Product_cat C C)) (@comp_cat_cov_func B C (Product_cat C C)
  (@product_diagonal_func C)) Z)) (@one_cat_uncopair_family_func B C C1 Prod t A T0 X Y Z)
  (@one_cat_copair_family_func B C C1 Prod t A T0 X Y Z)) ≡ @id_func (Hom_cat (Functor_cat B (Product_cat C C))
  (@Struct_sigma (Functor B C) (λ _ : τ (Functor B C), Functor B C) X Y) (@fapp0 (Functor_cat B C) (Functor_cat B
  (Product_cat C C)) (@comp_cat_cov_func B C (Product_cat C C) (@product_diagonal_func C)) Z));
assert [B C : Cat] (C1 : τ (IsNCat (cat_succ cat_zero) C))
  [Prod : τ (Functor (Product_cat C C) C)] [t : τ (Obj C)]
  (A : τ (@AdditiveCategory C Prod t)) (T0 : τ (@TerminalObject (Op_cat C) t)) (X Y Z : τ (Functor B C)) (h k : τ (Obj
  (Hom_cat (Functor_cat B (Product_cat C C)) (@Struct_sigma (Functor B C) (λ _ : τ (Functor B C), Functor B C) X Y)
  (@fapp0 (Functor_cat B C) (Functor_cat B (Product_cat C C)) (@comp_cat_cov_func B C (Product_cat C C)
  (@product_diagonal_func C)) Z)))) ⊢ @fapp1_func (Hom_cat (Functor_cat B (Product_cat C C)) (@Struct_sigma (Functor B
  C) (λ _ : τ (Functor B C), Functor B C) X Y) (@fapp0 (Functor_cat B C) (Functor_cat B (Product_cat C C))
  (@comp_cat_cov_func B C (Product_cat C C) (@product_diagonal_func C)) Z)) (Hom_cat (Functor_cat B (Product_cat C C))
  (@Struct_sigma (Functor B C) (λ _ : τ (Functor B C), Functor B C) X Y) (@fapp0 (Functor_cat B C) (Functor_cat B
  (Product_cat C C)) (@comp_cat_cov_func B C (Product_cat C C) (@product_diagonal_func C)) Z)) (@comp_cat_fapp0
  (Hom_cat (Functor_cat B (Product_cat C C)) (@Struct_sigma (Functor B C) (λ _ : τ (Functor B C), Functor B C) X Y)
  (@fapp0 (Functor_cat B C) (Functor_cat B (Product_cat C C)) (@comp_cat_cov_func B C (Product_cat C C)
  (@product_diagonal_func C)) Z)) (@Transf_cat B C (@fapp0 (Functor_cat B (Product_cat C C)) (Functor_cat B C)
  (@comp_cat_cov_func B (Product_cat C C) C Prod) (@Struct_sigma (Functor B C) (λ _ : τ (Functor B C), Functor B C) X
  Y)) Z) (Hom_cat (Functor_cat B (Product_cat C C)) (@Struct_sigma (Functor B C) (λ _ : τ (Functor B C), Functor B C)
  X Y) (@fapp0 (Functor_cat B C) (Functor_cat B (Product_cat C C)) (@comp_cat_cov_func B C (Product_cat C C)
  (@product_diagonal_func C)) Z)) (@one_cat_uncopair_family_func B C C1 Prod t A T0 X Y Z)
  (@one_cat_copair_family_func B C C1 Prod t A T0 X Y Z)) h k ≡ @id_func (Hom_cat (Hom_cat (Functor_cat B
  (Product_cat C C)) (@Struct_sigma (Functor B C) (λ _ : τ (Functor B C), Functor B C) X Y) (@fapp0 (Functor_cat B C)
  (Functor_cat B (Product_cat C C)) (@comp_cat_cov_func B C (Product_cat C C) (@product_diagonal_func C)) Z)) h k);
assert [B C : Cat] (C1 : τ (IsNCat (cat_succ cat_zero) C))
  [Prod : τ (Functor (Product_cat C C) C)] [t : τ (Obj C)]
  (A : τ (@AdditiveCategory C Prod t)) (T0 : τ (@TerminalObject (Op_cat C) t)) (X Y Z : τ (Functor B C)) (h k : τ (Obj
  (Hom_cat (Functor_cat B (Product_cat C C)) (@Struct_sigma (Functor B C) (λ _ : τ (Functor B C), Functor B C) X Y)
  (@fapp0 (Functor_cat B C) (Functor_cat B (Product_cat C C)) (@comp_cat_cov_func B C (Product_cat C C)
  (@product_diagonal_func C)) Z)))) (alpha : τ (Hom (Hom_cat (Functor_cat B (Product_cat C C)) (@Struct_sigma (Functor
  B C) (λ _ : τ (Functor B C), Functor B C) X Y) (@fapp0 (Functor_cat B C) (Functor_cat B (Product_cat C C))
  (@comp_cat_cov_func B C (Product_cat C C) (@product_diagonal_func C)) Z)) h k)) ⊢ @fapp1_fapp0 (Hom_cat (Functor_cat
  B (Product_cat C C)) (@Struct_sigma (Functor B C) (λ _ : τ (Functor B C), Functor B C) X Y) (@fapp0 (Functor_cat B
  C) (Functor_cat B (Product_cat C C)) (@comp_cat_cov_func B C (Product_cat C C) (@product_diagonal_func C)) Z))
  (Hom_cat (Functor_cat B (Product_cat C C)) (@Struct_sigma (Functor B C) (λ _ : τ (Functor B C), Functor B C) X Y)
  (@fapp0 (Functor_cat B C) (Functor_cat B (Product_cat C C)) (@comp_cat_cov_func B C (Product_cat C C)
  (@product_diagonal_func C)) Z)) (@comp_cat_fapp0 (Hom_cat (Functor_cat B (Product_cat C C)) (@Struct_sigma (Functor
  B C) (λ _ : τ (Functor B C), Functor B C) X Y) (@fapp0 (Functor_cat B C) (Functor_cat B (Product_cat C C))
  (@comp_cat_cov_func B C (Product_cat C C) (@product_diagonal_func C)) Z)) (@Transf_cat B C (@fapp0 (Functor_cat B
  (Product_cat C C)) (Functor_cat B C) (@comp_cat_cov_func B (Product_cat C C) C Prod) (@Struct_sigma (Functor B C) (λ
  _ : τ (Functor B C), Functor B C) X Y)) Z) (Hom_cat (Functor_cat B (Product_cat C C)) (@Struct_sigma (Functor B C)
  (λ _ : τ (Functor B C), Functor B C) X Y) (@fapp0 (Functor_cat B C) (Functor_cat B (Product_cat C C))
  (@comp_cat_cov_func B C (Product_cat C C) (@product_diagonal_func C)) Z)) (@one_cat_uncopair_family_func B C
  C1 Prod t A T0 X Y Z) (@one_cat_copair_family_func B C C1 Prod t A T0 X Y Z)) h k alpha ≡ alpha;

assert [B C : Cat] (C1 : τ (IsNCat (cat_succ cat_zero) C))
  [Prod : τ (Functor (Product_cat C C) C)] [t : τ (Obj C)]
  (A : τ (@AdditiveCategory C Prod t)) (T0 : τ (@TerminalObject (Op_cat C) t)) (X Y Z : τ (Functor B C)) ⊢
  (@comp_cat_fapp0 (@Transf_cat B C (@fapp0 (Functor_cat B (Product_cat C C)) (Functor_cat B C) (@comp_cat_cov_func B
  (Product_cat C C) C Prod) (@Struct_sigma (Functor B C) (λ _ : τ (Functor B C), Functor B C) X Y)) Z) (Hom_cat
  (Functor_cat B (Product_cat C C)) (@Struct_sigma (Functor B C) (λ _ : τ (Functor B C), Functor B C) X Y) (@fapp0
  (Functor_cat B C) (Functor_cat B (Product_cat C C)) (@comp_cat_cov_func B C (Product_cat C C)
  (@product_diagonal_func C)) Z)) (@Transf_cat B C (@fapp0 (Functor_cat B (Product_cat C C)) (Functor_cat B C)
  (@comp_cat_cov_func B (Product_cat C C) C Prod) (@Struct_sigma (Functor B C) (λ _ : τ (Functor B C), Functor B C) X
  Y)) Z) (@one_cat_copair_family_func B C C1 Prod t A T0 X Y Z) (@one_cat_uncopair_family_func B C C1 Prod
  t A T0 X Y Z)) ≡ @id_func (@Transf_cat B C (@fapp0 (Functor_cat B (Product_cat C C)) (Functor_cat B C)
  (@comp_cat_cov_func B (Product_cat C C) C Prod) (@Struct_sigma (Functor B C) (λ _ : τ (Functor B C), Functor B C) X
  Y)) Z);
assert [B C : Cat] (C1 : τ (IsNCat (cat_succ cat_zero) C))
  [Prod : τ (Functor (Product_cat C C) C)] [t : τ (Obj C)]
  (A : τ (@AdditiveCategory C Prod t)) (T0 : τ (@TerminalObject (Op_cat C) t)) (X Y Z : τ (Functor B C)) (h k : τ (Obj
  (@Transf_cat B C (@fapp0 (Functor_cat B (Product_cat C C)) (Functor_cat B C) (@comp_cat_cov_func B (Product_cat C C)
  C Prod) (@Struct_sigma (Functor B C) (λ _ : τ (Functor B C), Functor B C) X Y)) Z))) ⊢ @fapp1_func (@Transf_cat B C
  (@fapp0 (Functor_cat B (Product_cat C C)) (Functor_cat B C) (@comp_cat_cov_func B (Product_cat C C) C Prod)
  (@Struct_sigma (Functor B C) (λ _ : τ (Functor B C), Functor B C) X Y)) Z) (@Transf_cat B C (@fapp0 (Functor_cat B
  (Product_cat C C)) (Functor_cat B C) (@comp_cat_cov_func B (Product_cat C C) C Prod) (@Struct_sigma (Functor B C) (λ
  _ : τ (Functor B C), Functor B C) X Y)) Z) (@comp_cat_fapp0 (@Transf_cat B C (@fapp0 (Functor_cat B (Product_cat C
  C)) (Functor_cat B C) (@comp_cat_cov_func B (Product_cat C C) C Prod) (@Struct_sigma (Functor B C) (λ _ : τ (Functor
  B C), Functor B C) X Y)) Z) (Hom_cat (Functor_cat B (Product_cat C C)) (@Struct_sigma (Functor B C) (λ _ : τ
  (Functor B C), Functor B C) X Y) (@fapp0 (Functor_cat B C) (Functor_cat B (Product_cat C C)) (@comp_cat_cov_func B C
  (Product_cat C C) (@product_diagonal_func C)) Z)) (@Transf_cat B C (@fapp0 (Functor_cat B (Product_cat C C))
  (Functor_cat B C) (@comp_cat_cov_func B (Product_cat C C) C Prod) (@Struct_sigma (Functor B C) (λ _ : τ (Functor B
  C), Functor B C) X Y)) Z) (@one_cat_copair_family_func B C C1 Prod t A T0 X Y Z)
  (@one_cat_uncopair_family_func B C C1 Prod t A T0 X Y Z)) h k ≡ @id_func (Hom_cat (@Transf_cat B C (@fapp0
  (Functor_cat B (Product_cat C C)) (Functor_cat B C) (@comp_cat_cov_func B (Product_cat C C) C Prod) (@Struct_sigma
  (Functor B C) (λ _ : τ (Functor B C), Functor B C) X Y)) Z) h k);
assert [B C : Cat] (C1 : τ (IsNCat (cat_succ cat_zero) C))
  [Prod : τ (Functor (Product_cat C C) C)] [t : τ (Obj C)]
  (A : τ (@AdditiveCategory C Prod t)) (T0 : τ (@TerminalObject (Op_cat C) t)) (X Y Z : τ (Functor B C)) (h k : τ (Obj
  (@Transf_cat B C (@fapp0 (Functor_cat B (Product_cat C C)) (Functor_cat B C) (@comp_cat_cov_func B (Product_cat C C)
  C Prod) (@Struct_sigma (Functor B C) (λ _ : τ (Functor B C), Functor B C) X Y)) Z))) (alpha : τ (Hom (@Transf_cat B
  C (@fapp0 (Functor_cat B (Product_cat C C)) (Functor_cat B C) (@comp_cat_cov_func B (Product_cat C C) C Prod)
  (@Struct_sigma (Functor B C) (λ _ : τ (Functor B C), Functor B C) X Y)) Z) h k)) ⊢ @fapp1_fapp0 (@Transf_cat B C
  (@fapp0 (Functor_cat B (Product_cat C C)) (Functor_cat B C) (@comp_cat_cov_func B (Product_cat C C) C Prod)
  (@Struct_sigma (Functor B C) (λ _ : τ (Functor B C), Functor B C) X Y)) Z) (@Transf_cat B C (@fapp0 (Functor_cat B
  (Product_cat C C)) (Functor_cat B C) (@comp_cat_cov_func B (Product_cat C C) C Prod) (@Struct_sigma (Functor B C) (λ
  _ : τ (Functor B C), Functor B C) X Y)) Z) (@comp_cat_fapp0 (@Transf_cat B C (@fapp0 (Functor_cat B (Product_cat C
  C)) (Functor_cat B C) (@comp_cat_cov_func B (Product_cat C C) C Prod) (@Struct_sigma (Functor B C) (λ _ : τ (Functor
  B C), Functor B C) X Y)) Z) (Hom_cat (Functor_cat B (Product_cat C C)) (@Struct_sigma (Functor B C) (λ _ : τ
  (Functor B C), Functor B C) X Y) (@fapp0 (Functor_cat B C) (Functor_cat B (Product_cat C C)) (@comp_cat_cov_func B C
  (Product_cat C C) (@product_diagonal_func C)) Z)) (@Transf_cat B C (@fapp0 (Functor_cat B (Product_cat C C))
  (Functor_cat B C) (@comp_cat_cov_func B (Product_cat C C) C Prod) (@Struct_sigma (Functor B C) (λ _ : τ (Functor B
  C), Functor B C) X Y)) Z) (@one_cat_copair_family_func B C C1 Prod t A T0 X Y Z)
  (@one_cat_uncopair_family_func B C C1 Prod t A T0 X Y Z)) h k alpha ≡ alpha;

assert [B C : Cat] (C1 : τ (IsNCat (cat_succ cat_zero) C))
  [Prod : τ (Functor (Product_cat C C) C)] [t : τ (Obj C)]
  (A : τ (@AdditiveCategory C Prod t)) (T0 : τ (@TerminalObject (Op_cat C) t)) (X Y Z : τ (Functor B C)) (f : τ
  (@Transf B C X Z)) (g : τ (@Transf B C Y Z)) ⊢ (sigma_Fst (@one_cat_uncopair_family B C C1 Prod t A T0 X Y Z
  (@one_cat_copair_family B C C1 Prod t A T0 X Y Z f g))) ≡ f;
assert [B C : Cat] (C1 : τ (IsNCat (cat_succ cat_zero) C))
  [Prod : τ (Functor (Product_cat C C) C)] [t : τ (Obj C)]
  (A : τ (@AdditiveCategory C Prod t)) (T0 : τ (@TerminalObject (Op_cat C) t)) (X Y Z : τ (Functor B C)) (f : τ
  (@Transf B C X Z)) (g : τ (@Transf B C Y Z)) (b b1 : τ (Obj B)) (u : τ (Hom B b b1)) ⊢ @tapp1_fapp0 B C X Z b b1
  (sigma_Fst (@one_cat_uncopair_family B C C1 Prod t A T0 X Y Z (@one_cat_copair_family B C C1 Prod t A T0
  X Y Z f g))) u ≡ @tapp1_fapp0 B C X Z b b1 f u;
assert [B C : Cat] (C1 : τ (IsNCat (cat_succ cat_zero) C))
  [Prod : τ (Functor (Product_cat C C) C)] [t : τ (Obj C)]
  (A : τ (@AdditiveCategory C Prod t)) (T0 : τ (@TerminalObject (Op_cat C) t)) (X Y Z : τ (Functor B C)) (f : τ
  (@Transf B C X Z)) (g : τ (@Transf B C Y Z)) (b b1 : τ (Obj B)) ⊢ @tapp1_func B C X Z b b1 (sigma_Fst
  (@one_cat_uncopair_family B C C1 Prod t A T0 X Y Z (@one_cat_copair_family B C C1 Prod t A T0 X Y Z f
  g))) ≡ @tapp1_func B C X Z b b1 f;
assertnot [B C : Cat] (C1 : τ (IsNCat (cat_succ cat_zero) C))
  [Prod : τ (Functor (Product_cat C C) C)] [t : τ (Obj C)]
  (A : τ (@AdditiveCategory C Prod t)) (T0 : τ (@TerminalObject (Op_cat C) t)) (X Y Z : τ (Functor B C)) (f : τ
  (@Transf B C X Z)) (g : τ (@Transf B C Y Z)) (h0 : τ (@Transf B C X Z)) ⊢ @eq_refl (@Transf B C X Z) (sigma_Fst
  (@one_cat_uncopair_family B C C1 Prod t A T0 X Y Z (@one_cat_copair_family B C C1 Prod t A T0 X Y Z f
  g))) : τ (@= (@Transf B C X Z) (sigma_Fst (@one_cat_uncopair_family B C C1 Prod t A T0 X Y Z
  (@one_cat_copair_family B C C1 Prod t A T0 X Y Z f g))) h0);

assert [B C : Cat] (C1 : τ (IsNCat (cat_succ cat_zero) C))
  [Prod : τ (Functor (Product_cat C C) C)] [t : τ (Obj C)]
  (A : τ (@AdditiveCategory C Prod t)) (T0 : τ (@TerminalObject (Op_cat C) t)) (X Y Z : τ (Functor B C)) (f : τ
  (@Transf B C X Z)) (g : τ (@Transf B C Y Z)) ⊢ (sigma_Snd (@one_cat_uncopair_family B C C1 Prod t A T0 X Y Z
  (@one_cat_copair_family B C C1 Prod t A T0 X Y Z f g))) ≡ g;
assert [B C : Cat] (C1 : τ (IsNCat (cat_succ cat_zero) C))
  [Prod : τ (Functor (Product_cat C C) C)] [t : τ (Obj C)]
  (A : τ (@AdditiveCategory C Prod t)) (T0 : τ (@TerminalObject (Op_cat C) t)) (X Y Z : τ (Functor B C)) (f : τ
  (@Transf B C X Z)) (g : τ (@Transf B C Y Z)) (b b1 : τ (Obj B)) (u : τ (Hom B b b1)) ⊢ @tapp1_fapp0 B C Y Z b b1
  (sigma_Snd (@one_cat_uncopair_family B C C1 Prod t A T0 X Y Z (@one_cat_copair_family B C C1 Prod t A T0
  X Y Z f g))) u ≡ @tapp1_fapp0 B C Y Z b b1 g u;
assert [B C : Cat] (C1 : τ (IsNCat (cat_succ cat_zero) C))
  [Prod : τ (Functor (Product_cat C C) C)] [t : τ (Obj C)]
  (A : τ (@AdditiveCategory C Prod t)) (T0 : τ (@TerminalObject (Op_cat C) t)) (X Y Z : τ (Functor B C)) (f : τ
  (@Transf B C X Z)) (g : τ (@Transf B C Y Z)) (b b1 : τ (Obj B)) ⊢ @tapp1_func B C Y Z b b1 (sigma_Snd
  (@one_cat_uncopair_family B C C1 Prod t A T0 X Y Z (@one_cat_copair_family B C C1 Prod t A T0 X Y Z f
  g))) ≡ @tapp1_func B C Y Z b b1 g;
assertnot [B C : Cat] (C1 : τ (IsNCat (cat_succ cat_zero) C))
  [Prod : τ (Functor (Product_cat C C) C)] [t : τ (Obj C)]
  (A : τ (@AdditiveCategory C Prod t)) (T0 : τ (@TerminalObject (Op_cat C) t)) (X Y Z : τ (Functor B C)) (f : τ
  (@Transf B C X Z)) (g : τ (@Transf B C Y Z)) (h0 : τ (@Transf B C Y Z)) ⊢ @eq_refl (@Transf B C Y Z) (sigma_Snd
  (@one_cat_uncopair_family B C C1 Prod t A T0 X Y Z (@one_cat_copair_family B C C1 Prod t A T0 X Y Z f
  g))) : τ (@= (@Transf B C Y Z) (sigma_Snd (@one_cat_uncopair_family B C C1 Prod t A T0 X Y Z
  (@one_cat_copair_family B C C1 Prod t A T0 X Y Z f g))) h0);

assert [B C : Cat] (C1 : τ (IsNCat (cat_succ cat_zero) C))
  [Prod : τ (Functor (Product_cat C C) C)] [t : τ (Obj C)]
  (A : τ (@AdditiveCategory C Prod t)) (T0 : τ (@TerminalObject (Op_cat C) t)) (X Y Z : τ (Functor B C)) (f : τ
  (@Transf B C X Z)) (g : τ (@Transf B C Y Z)) (b : τ (Obj B))
  ⊢ @one_cat_copair_family_component_path B C C1 Prod t A T0 X Y Z f g b
    : τ (@= (Hom C (@fapp0 (Product_cat C C) C Prod (@Product_pair C C (@fapp0 B C X b) (@fapp0 B C Y b))) (@fapp0 B C
  Z b))
      (@tapp0_fapp0 B C (@fapp0 (Functor_cat B (Product_cat C C)) (Functor_cat B C) (@comp_cat_cov_func B (Product_cat
  C C) C Prod) (@Struct_sigma (Functor B C) (λ _ : τ (Functor B C), Functor B C) X Y)) Z b
  (@one_cat_copair_family B C C1 Prod t A T0 X Y Z f g))
      (@additive_copair_fapp0 C Prod t A (@fapp0 B C X b) (@fapp0 B C Y b) (@fapp0 B C Z b) (@tapp0_fapp0 B C X Z b f)
  (@tapp0_fapp0 B C Y Z b g)));
