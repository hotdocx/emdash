/* Native signed programs and whole composition laws, with original component data. */
require open emdash.emdash3_2_one_cat_difference_families;

assert [B C : Cat] (C1 : τ (IsNCat (cat_succ cat_zero) C)) [Prod : τ (Functor (Product_cat C C) C)] [t : τ (Obj C)] (A
  : τ (@AdditiveCategory C Prod t)) (T0 : τ (@TerminalObject (Op_cat C) t)) (X Y : τ (Functor B C)) (f : τ (@Transf B
  C X Y)) (b : τ (Obj B)) ⊢ @one_cat_negative_family_component_neg_path B C C1 Prod t A T0 X Y f b
  : τ (@= (Hom C (@fapp0 B C X b) (@fapp0 B C Y b)) (@tapp0_fapp0 B C X Y b (@one_cat_negative_family B C C1
  Prod t A T0 X Y f)) (@preadditive_hom_neg C (@additive_preadditive C Prod t A) (@fapp0 B C X b) (@fapp0 B C Y b)
  (@tapp0_fapp0 B C X Y b f)));
assert [B C : Cat] (C1 : τ (IsNCat (cat_succ cat_zero) C)) [Prod : τ (Functor (Product_cat C C) C)] [t : τ (Obj C)] (A
  : τ (@AdditiveCategory C Prod t)) (T0 : τ (@TerminalObject (Op_cat C) t)) (X Y : τ (Functor B C)) (f : τ (@Transf B
  C X Y)) ⊢ @one_cat_negative_family_centrality_path B C C1 Prod t A T0 X Y f
  : τ (@= (@Transf B C X Y) (@comp_fapp0 (Functor_cat B C) X X Y f (@one_cat_negative_family_transf B C C1 Prod
  t A T0 X)) (@comp_fapp0 (Functor_cat B C) X Y Y (@one_cat_negative_family_transf B C C1 Prod t A T0 Y) f));
assert [B C : Cat] (C1 : τ (IsNCat (cat_succ cat_zero) C)) [Prod : τ (Functor (Product_cat C C) C)] [t : τ (Obj C)] (A
  : τ (@AdditiveCategory C Prod t)) (T0 : τ (@TerminalObject (Op_cat C) t)) (X Y Z : τ (Functor B C)) (f : τ (@Transf
  B C X Y)) (g : τ (@Transf B C Y Z)) ⊢ @one_cat_negative_family_precompose_path B C C1 Prod t A T0 X Y Z f g :
  τ (@= (@Transf B C X Z) (@one_cat_negative_family B C C1 Prod t A T0 X Z (@comp_fapp0 (Functor_cat B C) X Y Z
  g f)) (@comp_fapp0 (Functor_cat B C) X Y Z (@one_cat_negative_family B C C1 Prod t A T0 Y Z g) f));
assert [B C : Cat] (C1 : τ (IsNCat (cat_succ cat_zero) C)) [Prod : τ (Functor (Product_cat C C) C)] [t : τ (Obj C)] (A
  : τ (@AdditiveCategory C Prod t)) (T0 : τ (@TerminalObject (Op_cat C) t)) (X Y Z : τ (Functor B C)) (f : τ (@Transf
  B C X Y)) (g : τ (@Transf B C Y Z)) ⊢ @one_cat_negative_family_postcompose_path B C C1 Prod t A T0 X Y Z f g :
  τ (@= (@Transf B C X Z) (@one_cat_negative_family B C C1 Prod t A T0 X Z (@comp_fapp0 (Functor_cat B C) X Y Z
  g f)) (@comp_fapp0 (Functor_cat B C) X Y Z g (@one_cat_negative_family B C C1 Prod t A T0 X Y f)));
assert [B C : Cat] (C1 : τ (IsNCat (cat_succ cat_zero) C)) [Prod : τ (Functor (Product_cat C C) C)] [t : τ (Obj C)] (A
  : τ (@AdditiveCategory C Prod t)) (T0 : τ (@TerminalObject (Op_cat C) t)) (X Y : τ (Functor B C)) (u v : τ (Obj
  (@Transf_cat B C X Y))) ⊢ @fapp1_func (@Transf_cat B C X Y) (@Transf_cat B C X Y)
  (@one_cat_negative_family_func B C C1 Prod t A T0 X Y) u v : τ (Functor (Hom_cat (@Transf_cat B C X Y) u v)
  (Hom_cat (@Transf_cat B C X Y) (@fapp0 (@Transf_cat B C X Y) (@Transf_cat B C X Y)
  (@one_cat_negative_family_func B C C1 Prod t A T0 X Y) u) (@fapp0 (@Transf_cat B C X Y) (@Transf_cat B C X Y)
  (@one_cat_negative_family_func B C C1 Prod t A T0 X Y) v)));
assert [B C : Cat] (C1 : τ (IsNCat (cat_succ cat_zero) C)) [Prod : τ (Functor (Product_cat C C) C)] [t : τ (Obj C)] (A
  : τ (@AdditiveCategory C Prod t)) (T0 : τ (@TerminalObject (Op_cat C) t)) (X Y : τ (Functor B C)) (u v : τ (Obj
  (@Transf_cat B C X Y))) (alpha : τ (Hom (@Transf_cat B C X Y) u v)) ⊢ @fapp1_fapp0 (@Transf_cat B C X Y)
  (@Transf_cat B C X Y) (@one_cat_negative_family_func B C C1 Prod t A T0 X Y) u v alpha : τ (Hom (@Transf_cat B
  C X Y) (@fapp0 (@Transf_cat B C X Y) (@Transf_cat B C X Y) (@one_cat_negative_family_func B C C1 Prod t A T0 X
  Y) u) (@fapp0 (@Transf_cat B C X Y) (@Transf_cat B C X Y) (@one_cat_negative_family_func B C C1 Prod t A T0 X
  Y) v));
assert [B C : Cat] (C1 : τ (IsNCat (cat_succ cat_zero) C)) [Prod : τ (Functor (Product_cat C C) C)] [t : τ (Obj C)] (A
  : τ (@AdditiveCategory C Prod t)) (T0 : τ (@TerminalObject (Op_cat C) t)) (X Y : τ (Functor B C)) (u v : τ (Obj
  (Product_cat (@Transf_cat B C X Y) (@Transf_cat B C X Y)))) ⊢ @fapp1_func (Product_cat (@Transf_cat B C X Y)
  (@Transf_cat B C X Y)) (@Transf_cat B C X Y) (@one_cat_difference_family_func B C C1 Prod t A T0 X Y) u v : τ
  (Functor (Hom_cat (Product_cat (@Transf_cat B C X Y) (@Transf_cat B C X Y)) u v) (Hom_cat (@Transf_cat B C X Y)
  (@fapp0 (Product_cat (@Transf_cat B C X Y) (@Transf_cat B C X Y)) (@Transf_cat B C X Y)
  (@one_cat_difference_family_func B C C1 Prod t A T0 X Y) u) (@fapp0 (Product_cat (@Transf_cat B C X Y)
  (@Transf_cat B C X Y)) (@Transf_cat B C X Y) (@one_cat_difference_family_func B C C1 Prod t A T0 X Y) v)));
assert [B C : Cat] (C1 : τ (IsNCat (cat_succ cat_zero) C)) [Prod : τ (Functor (Product_cat C C) C)] [t : τ (Obj C)] (A
  : τ (@AdditiveCategory C Prod t)) (T0 : τ (@TerminalObject (Op_cat C) t)) (X Y : τ (Functor B C)) (u v : τ (Obj
  (Product_cat (@Transf_cat B C X Y) (@Transf_cat B C X Y)))) (alpha : τ (Hom (Product_cat (@Transf_cat B C X Y)
  (@Transf_cat B C X Y)) u v)) ⊢ @fapp1_fapp0 (Product_cat (@Transf_cat B C X Y) (@Transf_cat B C X Y)) (@Transf_cat B
  C X Y) (@one_cat_difference_family_func B C C1 Prod t A T0 X Y) u v alpha : τ (Hom (@Transf_cat B C X Y)
  (@fapp0 (Product_cat (@Transf_cat B C X Y) (@Transf_cat B C X Y)) (@Transf_cat B C X Y)
  (@one_cat_difference_family_func B C C1 Prod t A T0 X Y) u) (@fapp0 (Product_cat (@Transf_cat B C X Y)
  (@Transf_cat B C X Y)) (@Transf_cat B C X Y) (@one_cat_difference_family_func B C C1 Prod t A T0 X Y) v));
assert [B C : Cat] (C1 : τ (IsNCat (cat_succ cat_zero) C)) [Prod : τ (Functor (Product_cat C C) C)] [t : τ (Obj C)] (A
  : τ (@AdditiveCategory C Prod t)) (T0 : τ (@TerminalObject (Op_cat C) t)) (X Y : τ (Functor B C)) (f : τ (@Transf B
  C X Y)) (g : τ (@Transf B C X Y)) ⊢ @one_cat_difference_family_formula_path B C C1 Prod t A T0 X Y f g : τ (@=
  (@Transf B C X Y) (@one_cat_difference_family B C C1 Prod t A T0 X Y f g) (@one_cat_additive_family_add B C C1
  Prod t A T0 X Y f (@one_cat_negative_family B C C1 Prod t A T0 X Y g)));
assert [B C : Cat] (C1 : τ (IsNCat (cat_succ cat_zero) C)) [Prod : τ (Functor (Product_cat C C) C)] [t : τ (Obj C)] (A
  : τ (@AdditiveCategory C Prod t)) (T0 : τ (@TerminalObject (Op_cat C) t)) (X Y : τ (Functor B C)) (f : τ (@Transf B
  C X Y)) (g : τ (@Transf B C X Y)) (b : τ (Obj B)) ⊢ @one_cat_difference_family_component_path B C C1 Prod t A
  T0 X Y f g b : τ (@= (Hom C (@fapp0 B C X b) (@fapp0 B C Y b)) (@tapp0_fapp0 B C X Y b
  (@one_cat_difference_family B C C1 Prod t A T0 X Y f g)) (@preadditive_hom_add C (@additive_preadditive C Prod
  t A) (@fapp0 B C X b) (@fapp0 B C Y b) (@tapp0_fapp0 B C X Y b f) (@preadditive_hom_neg C (@additive_preadditive C
  Prod t A) (@fapp0 B C X b) (@fapp0 B C Y b) (@tapp0_fapp0 B C X Y b g))));
assertnot [B C : Cat] (C1 : τ (IsNCat (cat_succ cat_zero) C)) [Prod : τ (Functor (Product_cat C C) C)] [t : τ (Obj C)]
  (A : τ (@AdditiveCategory C Prod t)) (T0 : τ (@TerminalObject (Op_cat C) t)) (X Y : τ (Functor B C)) (f : τ (@Transf
  B C X Y)) (v : τ (@Transf B C X Y)) ⊢ @eq_refl (@Transf B C X Y) (@one_cat_negative_family B C C1 Prod t A T0
  X Y f) : τ (@= (@Transf B C X Y) (@one_cat_negative_family B C C1 Prod t A T0 X Y f) v);
assertnot [B C : Cat] (C1 : τ (IsNCat (cat_succ cat_zero) C)) [Prod : τ (Functor (Product_cat C C) C)] [t : τ (Obj C)]
  (A : τ (@AdditiveCategory C Prod t)) (T0 : τ (@TerminalObject (Op_cat C) t)) (X Y : τ (Functor B C)) (f : τ (@Transf
  B C X Y)) (g v : τ (@Transf B C X Y)) ⊢ @eq_refl (@Transf B C X Y) (@one_cat_difference_family B C C1 Prod t A
  T0 X Y f g) : τ (@= (@Transf B C X Y) (@one_cat_difference_family B C C1 Prod t A T0 X Y f g) v);
