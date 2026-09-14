/* Whole shear inverse, native component selection, and retained base action. */
require open emdash.emdash3_2_one_cat_negative_identity;

assert [B C : Cat] (C1 : τ (IsNCat (cat_succ cat_zero) C)) [Prod : τ (Functor (Product_cat C C) C)] [t : τ (Obj C)] (A
  : τ (@AdditiveCategory C Prod t)) (T0 : τ (@TerminalObject (Op_cat C) t)) (X : τ (Functor B C)) ⊢
  @omega_equiv_along_left_law (Functor_cat B C) (@fapp0 (Functor_cat B (Product_cat C C)) (Functor_cat B C)
  (@comp_cat_cov_func B (Product_cat C C) C Prod) (@Struct_sigma (Functor B C) (λ _ : τ (Functor B C), Functor B C) X
  X)) (@fapp0 (Functor_cat B (Product_cat C C)) (Functor_cat B C) (@comp_cat_cov_func B (Product_cat C C) C Prod)
  (@Struct_sigma (Functor B C) (λ _ : τ (Functor B C), Functor B C) X X)) (@one_cat_shear_family B C C1 Prod t A
  T0 X) (@one_cat_shear_family_omega B C C1 Prod t A T0 X) : τ (@= (@Transf B C (@fapp0 (Functor_cat B
  (Product_cat C C)) (Functor_cat B C) (@comp_cat_cov_func B (Product_cat C C) C Prod) (@Struct_sigma (Functor B C) (λ
  _ : τ (Functor B C), Functor B C) X X)) (@fapp0 (Functor_cat B (Product_cat C C)) (Functor_cat B C)
  (@comp_cat_cov_func B (Product_cat C C) C Prod) (@Struct_sigma (Functor B C) (λ _ : τ (Functor B C), Functor B C) X
  X))) (@comp_fapp0 (Functor_cat B C) (@fapp0 (Functor_cat B (Product_cat C C)) (Functor_cat B C) (@comp_cat_cov_func
  B (Product_cat C C) C Prod) (@Struct_sigma (Functor B C) (λ _ : τ (Functor B C), Functor B C) X X)) (@fapp0
  (Functor_cat B (Product_cat C C)) (Functor_cat B C) (@comp_cat_cov_func B (Product_cat C C) C Prod) (@Struct_sigma
  (Functor B C) (λ _ : τ (Functor B C), Functor B C) X X)) (@fapp0 (Functor_cat B (Product_cat C C)) (Functor_cat B C)
  (@comp_cat_cov_func B (Product_cat C C) C Prod) (@Struct_sigma (Functor B C) (λ _ : τ (Functor B C), Functor B C) X
  X)) (@one_cat_shear_family_inverse B C C1 Prod t A T0 X) (@one_cat_shear_family B C C1 Prod t A T0 X))
  (@id (Functor_cat B C) (@fapp0 (Functor_cat B (Product_cat C C)) (Functor_cat B C) (@comp_cat_cov_func B
  (Product_cat C C) C Prod) (@Struct_sigma (Functor B C) (λ _ : τ (Functor B C), Functor B C) X X))));
assert [B C : Cat] (C1 : τ (IsNCat (cat_succ cat_zero) C)) [Prod : τ (Functor (Product_cat C C) C)] [t : τ (Obj C)] (A
  : τ (@AdditiveCategory C Prod t)) (T0 : τ (@TerminalObject (Op_cat C) t)) (X : τ (Functor B C)) ⊢
  @omega_equiv_left_as_right_law (Functor_cat B C) (@fapp0 (Functor_cat B (Product_cat C C)) (Functor_cat B C)
  (@comp_cat_cov_func B (Product_cat C C) C Prod) (@Struct_sigma (Functor B C) (λ _ : τ (Functor B C), Functor B C) X
  X)) (@fapp0 (Functor_cat B (Product_cat C C)) (Functor_cat B C) (@comp_cat_cov_func B (Product_cat C C) C Prod)
  (@Struct_sigma (Functor B C) (λ _ : τ (Functor B C), Functor B C) X X)) (@one_cat_shear_family B C C1 Prod t A
  T0 X) (@one_cat_shear_family_omega B C C1 Prod t A T0 X) : τ (@= (@Transf B C (@fapp0 (Functor_cat B
  (Product_cat C C)) (Functor_cat B C) (@comp_cat_cov_func B (Product_cat C C) C Prod) (@Struct_sigma (Functor B C) (λ
  _ : τ (Functor B C), Functor B C) X X)) (@fapp0 (Functor_cat B (Product_cat C C)) (Functor_cat B C)
  (@comp_cat_cov_func B (Product_cat C C) C Prod) (@Struct_sigma (Functor B C) (λ _ : τ (Functor B C), Functor B C) X
  X))) (@comp_fapp0 (Functor_cat B C) (@fapp0 (Functor_cat B (Product_cat C C)) (Functor_cat B C) (@comp_cat_cov_func
  B (Product_cat C C) C Prod) (@Struct_sigma (Functor B C) (λ _ : τ (Functor B C), Functor B C) X X)) (@fapp0
  (Functor_cat B (Product_cat C C)) (Functor_cat B C) (@comp_cat_cov_func B (Product_cat C C) C Prod) (@Struct_sigma
  (Functor B C) (λ _ : τ (Functor B C), Functor B C) X X)) (@fapp0 (Functor_cat B (Product_cat C C)) (Functor_cat B C)
  (@comp_cat_cov_func B (Product_cat C C) C Prod) (@Struct_sigma (Functor B C) (λ _ : τ (Functor B C), Functor B C) X
  X)) (@one_cat_shear_family B C C1 Prod t A T0 X) (@one_cat_shear_family_inverse B C C1 Prod t A T0 X))
  (@id (Functor_cat B C) (@fapp0 (Functor_cat B (Product_cat C C)) (Functor_cat B C) (@comp_cat_cov_func B
  (Product_cat C C) C Prod) (@Struct_sigma (Functor B C) (λ _ : τ (Functor B C), Functor B C) X X))));
assert [B C : Cat] (C1 : τ (IsNCat (cat_succ cat_zero) C)) [Prod : τ (Functor (Product_cat C C) C)] [t : τ (Obj C)] (A
  : τ (@AdditiveCategory C Prod t)) (T0 : τ (@TerminalObject (Op_cat C) t)) (X : τ (Functor B C)) (b : τ (Obj B))
  ⊢ @tapp0_fapp0 B C (@fapp0 (Functor_cat B (Product_cat C C)) (Functor_cat B C) (@comp_cat_cov_func B (Product_cat C
  C) C Prod) (@Struct_sigma (Functor B C) (λ _ : τ (Functor B C), Functor B C) X X)) (@fapp0 (Functor_cat B
  (Product_cat C C)) (Functor_cat B C) (@comp_cat_cov_func B (Product_cat C C) C Prod) (@Struct_sigma (Functor B C) (λ
  _ : τ (Functor B C), Functor B C) X X)) b (@one_cat_shear_family_inverse B C C1 Prod t A T0 X) ≡
  @additive_shear_inverse C Prod t A (@fapp0 B C X b);
assert [B C : Cat] (C1 : τ (IsNCat (cat_succ cat_zero) C)) [Prod : τ (Functor (Product_cat C C) C)] [t : τ (Obj C)] (A
  : τ (@AdditiveCategory C Prod t)) (T0 : τ (@TerminalObject (Op_cat C) t)) (X : τ (Functor B C)) (b : τ (Obj B))
  ⊢ @one_cat_shear_family_component_path B C C1 Prod t A T0 X b
    : τ (@= (Hom C (@fapp0 (Product_cat C C) C Prod (@Product_pair C C (@fapp0 B C X b) (@fapp0 B C X b))) (@fapp0
  (Product_cat C C) C Prod (@Product_pair C C (@fapp0 B C X b) (@fapp0 B C X b)))) (@tapp0_fapp0 B C (@fapp0
  (Functor_cat B (Product_cat C C)) (Functor_cat B C) (@comp_cat_cov_func B (Product_cat C C) C Prod) (@Struct_sigma
  (Functor B C) (λ _ : τ (Functor B C), Functor B C) X X)) (@fapp0 (Functor_cat B (Product_cat C C)) (Functor_cat B C)
  (@comp_cat_cov_func B (Product_cat C C) C Prod) (@Struct_sigma (Functor B C) (λ _ : τ (Functor B C), Functor B C) X
  X)) b (@one_cat_shear_family B C C1 Prod t A T0 X)) (@additive_shear C Prod t A (@fapp0 B C X b)));
assert [B C : Cat] (C1 : τ (IsNCat (cat_succ cat_zero) C)) [Prod : τ (Functor (Product_cat C C) C)] [t : τ (Obj C)] (A
  : τ (@AdditiveCategory C Prod t)) (T0 : τ (@TerminalObject (Op_cat C) t)) (X : τ (Functor B C)) (b c : τ (Obj B))
  ⊢ @tapp1_func B C (@fapp0 (Functor_cat B (Product_cat C C)) (Functor_cat B C) (@comp_cat_cov_func B (Product_cat C
  C) C Prod) (@Struct_sigma (Functor B C) (λ _ : τ (Functor B C), Functor B C) X X)) (@fapp0 (Functor_cat B
  (Product_cat C C)) (Functor_cat B C) (@comp_cat_cov_func B (Product_cat C C) C Prod) (@Struct_sigma (Functor B C) (λ
  _ : τ (Functor B C), Functor B C) X X)) b c (@one_cat_shear_family_inverse B C C1 Prod t A T0 X)
    : τ (Functor (Hom_cat B b c) (Hom_cat C (@fapp0 B C (@fapp0 (Functor_cat B (Product_cat C C)) (Functor_cat B C)
  (@comp_cat_cov_func B (Product_cat C C) C Prod) (@Struct_sigma (Functor B C) (λ _ : τ (Functor B C), Functor B C) X
  X)) b) (@fapp0 B C (@fapp0 (Functor_cat B (Product_cat C C)) (Functor_cat B C) (@comp_cat_cov_func B (Product_cat C
  C) C Prod) (@Struct_sigma (Functor B C) (λ _ : τ (Functor B C), Functor B C) X X)) c)));
assert [B C : Cat] (C1 : τ (IsNCat (cat_succ cat_zero) C)) [Prod : τ (Functor (Product_cat C C) C)] [t : τ (Obj C)] (A
  : τ (@AdditiveCategory C Prod t)) (T0 : τ (@TerminalObject (Op_cat C) t)) (X : τ (Functor B C)) (b c : τ (Obj B)) (u
  : τ (Hom B b c))
  ⊢ @tapp1_fapp0 B C (@fapp0 (Functor_cat B (Product_cat C C)) (Functor_cat B C) (@comp_cat_cov_func B (Product_cat C
  C) C Prod) (@Struct_sigma (Functor B C) (λ _ : τ (Functor B C), Functor B C) X X)) (@fapp0 (Functor_cat B
  (Product_cat C C)) (Functor_cat B C) (@comp_cat_cov_func B (Product_cat C C) C Prod) (@Struct_sigma (Functor B C) (λ
  _ : τ (Functor B C), Functor B C) X X)) b c (@one_cat_shear_family_inverse B C C1 Prod t A T0 X) u : τ (Hom C
  (@fapp0 B C (@fapp0 (Functor_cat B (Product_cat C C)) (Functor_cat B C) (@comp_cat_cov_func B (Product_cat C C) C
  Prod) (@Struct_sigma (Functor B C) (λ _ : τ (Functor B C), Functor B C) X X)) b) (@fapp0 B C (@fapp0 (Functor_cat B
  (Product_cat C C)) (Functor_cat B C) (@comp_cat_cov_func B (Product_cat C C) C Prod) (@Struct_sigma (Functor B C) (λ
  _ : τ (Functor B C), Functor B C) X X)) c));
assertnot [B C : Cat] (C1 : τ (IsNCat (cat_succ cat_zero) C)) [Prod : τ (Functor (Product_cat C C) C)] [t : τ (Obj C)]
  (A : τ (@AdditiveCategory C Prod t)) (T0 : τ (@TerminalObject (Op_cat C) t)) (X : τ (Functor B C)) (b : τ (Obj B))
  (h : τ (Hom C (@fapp0 (Product_cat C C) C Prod (@Product_pair C C (@fapp0 B C X b) (@fapp0 B C X b))) (@fapp0
  (Product_cat C C) C Prod (@Product_pair C C (@fapp0 B C X b) (@fapp0 B C X b)))))
  ⊢ @eq_refl (Hom C (@fapp0 (Product_cat C C) C Prod (@Product_pair C C (@fapp0 B C X b) (@fapp0 B C X b))) (@fapp0
  (Product_cat C C) C Prod (@Product_pair C C (@fapp0 B C X b) (@fapp0 B C X b)))) (@tapp0_fapp0 B C (@fapp0
  (Functor_cat B (Product_cat C C)) (Functor_cat B C) (@comp_cat_cov_func B (Product_cat C C) C Prod) (@Struct_sigma
  (Functor B C) (λ _ : τ (Functor B C), Functor B C) X X)) (@fapp0 (Functor_cat B (Product_cat C C)) (Functor_cat B C)
  (@comp_cat_cov_func B (Product_cat C C) C Prod) (@Struct_sigma (Functor B C) (λ _ : τ (Functor B C), Functor B C) X
  X)) b (@one_cat_shear_family_inverse B C C1 Prod t A T0 X))
    : τ (@= (Hom C (@fapp0 (Product_cat C C) C Prod (@Product_pair C C (@fapp0 B C X b) (@fapp0 B C X b))) (@fapp0
  (Product_cat C C) C Prod (@Product_pair C C (@fapp0 B C X b) (@fapp0 B C X b)))) (@tapp0_fapp0 B C (@fapp0
  (Functor_cat B (Product_cat C C)) (Functor_cat B C) (@comp_cat_cov_func B (Product_cat C C) C Prod) (@Struct_sigma
  (Functor B C) (λ _ : τ (Functor B C), Functor B C) X X)) (@fapp0 (Functor_cat B (Product_cat C C)) (Functor_cat B C)
  (@comp_cat_cov_func B (Product_cat C C) C Prod) (@Struct_sigma (Functor B C) (λ _ : τ (Functor B C), Functor B C) X
  X)) b (@one_cat_shear_family_inverse B C C1 Prod t A T0 X)) h);
assert [C : Cat] (C1 : τ (IsNCat (cat_succ cat_zero) C)) [Prod : τ (Functor (Product_cat C C) C)] [t : τ (Obj C)] (A :
  τ (@AdditiveCategory C Prod t)) (T0 : τ (@TerminalObject (Op_cat C) t)) (x : τ (Obj C)) ⊢
  @additive_shear_left_path C Prod t A x : τ (@= (Hom C (@fapp0 (Product_cat C C) C Prod (@Product_pair C C x
  x)) (@fapp0 (Product_cat C C) C Prod (@Product_pair C C x x))) (@comp_fapp0 C (@fapp0 (Product_cat C C) C Prod
  (@Product_pair C C x x)) (@fapp0 (Product_cat C C) C Prod (@Product_pair C C x x)) (@fapp0 (Product_cat C C) C Prod
  (@Product_pair C C x x)) (@additive_shear_inverse C Prod t A x) (@additive_shear C Prod t A x)) (@id C
  (@fapp0 (Product_cat C C) C Prod (@Product_pair C C x x))));
assert [C : Cat] (C1 : τ (IsNCat (cat_succ cat_zero) C)) [Prod : τ (Functor (Product_cat C C) C)] [t : τ (Obj C)] (A :
  τ (@AdditiveCategory C Prod t)) (T0 : τ (@TerminalObject (Op_cat C) t)) (x : τ (Obj C)) ⊢
  @additive_shear_right_path C Prod t A x : τ (@= (Hom C (@fapp0 (Product_cat C C) C Prod (@Product_pair C C x
  x)) (@fapp0 (Product_cat C C) C Prod (@Product_pair C C x x))) (@comp_fapp0 C (@fapp0 (Product_cat C C) C Prod
  (@Product_pair C C x x)) (@fapp0 (Product_cat C C) C Prod (@Product_pair C C x x)) (@fapp0 (Product_cat C C) C Prod
  (@Product_pair C C x x)) (@additive_shear C Prod t A x) (@additive_shear_inverse C Prod t A x)) (@id C
  (@fapp0 (Product_cat C C) C Prod (@Product_pair C C x x))));
