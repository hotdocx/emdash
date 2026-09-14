/* Whole addition and original-component readback. */
require open emdash.emdash3_2_one_cat_additive_family_paths;

assert [B C : Cat] (C1 : τ (IsNCat (cat_succ cat_zero) C))
  [Prod : τ (Functor (Product_cat C C) C)] [t : τ (Obj C)]
  (A : τ (@AdditiveCategory C Prod t)) (T0 : τ (@TerminalObject (Op_cat C) t)) (X Y : τ (Functor B C)) (f g : τ
  (@Transf B C X Y)) ⊢ @one_cat_additive_family_add_formula_path B C C1 Prod t A T0 X Y f g
  : τ (@= (@Transf B C X Y) (@one_cat_additive_family_add B C C1 Prod t A T0 X Y f g) (@comp_fapp0 (Functor_cat
  B C) X (@fapp0 (Functor_cat B (Product_cat C C)) (Functor_cat B C) (@comp_cat_cov_func B (Product_cat C C) C Prod)
  (@Struct_sigma (Functor B C) (λ _ : τ (Functor B C), Functor B C) X X)) Y (@one_cat_copair_family B C C1 Prod
  t A T0 X X Y f g) (@one_cat_product_family_pair B C C1 Prod (@additive_binary_products C Prod t A) X X X (@id
  (Functor_cat B C) X) (@id (Functor_cat B C) X))));
assert [B C : Cat] (C1 : τ (IsNCat (cat_succ cat_zero) C))
  [Prod : τ (Functor (Product_cat C C) C)] [t : τ (Obj C)]
  (A : τ (@AdditiveCategory C Prod t)) (T0 : τ (@TerminalObject (Op_cat C) t)) (X Y : τ (Functor B C)) (f g : τ
  (@Transf B C X Y)) (b : τ (Obj B)) ⊢ @one_cat_additive_family_add_component_path B C C1 Prod t A T0 X Y f g b
  : τ (@= (Hom C (@fapp0 B C X b) (@fapp0 B C Y b)) (@tapp0_fapp0 B C X Y b (@one_cat_additive_family_add B C C1
  Prod t A T0 X Y f g)) (@preadditive_hom_add C (@additive_preadditive C Prod t A) (@fapp0 B C X b) (@fapp0 B C Y b)
  (@tapp0_fapp0 B C X Y b f) (@tapp0_fapp0 B C X Y b g)));
assert [B C : Cat] (C1 : τ (IsNCat (cat_succ cat_zero) C))
  [Prod : τ (Functor (Product_cat C C) C)] [t : τ (Obj C)]
  (A : τ (@AdditiveCategory C Prod t)) (T0 : τ (@TerminalObject (Op_cat C) t)) (X Y : τ (Functor B C)) (u v : τ (Obj
  (Product_cat (@Transf_cat B C X Y) (@Transf_cat B C X Y))))
  ⊢ @fapp1_func (Product_cat (@Transf_cat B C X Y) (@Transf_cat B C X Y)) (@Transf_cat B C X Y)
  (@one_cat_additive_family_add_func B C C1 Prod t A T0 X Y) u v
    : τ (Functor (Hom_cat (Product_cat (@Transf_cat B C X Y) (@Transf_cat B C X Y)) u v) (Hom_cat (@Transf_cat B C X
  Y) (@fapp0 (Product_cat (@Transf_cat B C X Y) (@Transf_cat B C X Y)) (@Transf_cat B C X Y)
  (@one_cat_additive_family_add_func B C C1 Prod t A T0 X Y) u) (@fapp0 (Product_cat (@Transf_cat B C X Y)
  (@Transf_cat B C X Y)) (@Transf_cat B C X Y) (@one_cat_additive_family_add_func B C C1 Prod t A T0 X Y) v)));
assert [B C : Cat] (C1 : τ (IsNCat (cat_succ cat_zero) C))
  [Prod : τ (Functor (Product_cat C C) C)] [t : τ (Obj C)]
  (A : τ (@AdditiveCategory C Prod t)) (T0 : τ (@TerminalObject (Op_cat C) t)) (X Y : τ (Functor B C)) (u v : τ (Obj
  (Product_cat (@Transf_cat B C X Y) (@Transf_cat B C X Y)))) (alpha : τ (Hom (Product_cat (@Transf_cat B C X Y)
  (@Transf_cat B C X Y)) u v))
  ⊢ @fapp1_fapp0 (Product_cat (@Transf_cat B C X Y) (@Transf_cat B C X Y)) (@Transf_cat B C X Y)
  (@one_cat_additive_family_add_func B C C1 Prod t A T0 X Y) u v alpha
    : τ (Hom (@Transf_cat B C X Y) (@fapp0 (Product_cat (@Transf_cat B C X Y) (@Transf_cat B C X Y)) (@Transf_cat B C
  X Y) (@one_cat_additive_family_add_func B C C1 Prod t A T0 X Y) u) (@fapp0 (Product_cat (@Transf_cat B C X Y)
  (@Transf_cat B C X Y)) (@Transf_cat B C X Y) (@one_cat_additive_family_add_func B C C1 Prod t A T0 X Y) v));
assertnot [B C : Cat] (C1 : τ (IsNCat (cat_succ cat_zero) C))
  [Prod : τ (Functor (Product_cat C C) C)] [t : τ (Obj C)]
  (A : τ (@AdditiveCategory C Prod t)) (T0 : τ (@TerminalObject (Op_cat C) t)) (X Y : τ (Functor B C)) (f g : τ
  (@Transf B C X Y)) (h : τ (@Transf B C X Y)) ⊢ @eq_refl (@Transf B C X Y) (@one_cat_additive_family_add B C C1
  Prod t A T0 X Y f g)
  : τ (@= (@Transf B C X Y) (@one_cat_additive_family_add B C C1 Prod t A T0 X Y f g) h);
