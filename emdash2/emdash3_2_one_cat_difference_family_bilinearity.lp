require open emdash.emdash3_2_one_cat_additive_family_bilinearity;
require open emdash.emdash3_2_one_cat_difference_families;

/* Whole subtraction inherits both composition laws from native addition and negation. */

// precomposition preserves the original whole difference.
symbol one_cat_difference_family_precompose_path [B C : Cat] (C1 : τ (IsNCat (cat_succ cat_zero) C)) [Prod : τ
  (Functor (Product_cat C C) C)] [t : τ (Obj C)] (A : τ (@AdditiveCategory C Prod t)) (T0 : τ (@TerminalObject (Op_cat
  C) t)) (W X Y : τ (Functor B C)) (f g : τ (@Transf B C X Y)) (h : τ (@Transf B C W X))
  : τ (@= (@Transf B C W Y) (@comp_fapp0 (Functor_cat B C) W X Y (@one_cat_difference_family B C C1 Prod t A T0 X Y f
  g) h) (@one_cat_difference_family B C C1 Prod t A T0 W Y (@comp_fapp0 (Functor_cat B C) W X Y f h) (@comp_fapp0
  (Functor_cat B C) W X Y g h)))
≔ (@eq_trans (@Transf B C W Y) (@comp_fapp0 (Functor_cat B C) W X Y (@one_cat_difference_family B C C1 Prod t A T0 X Y
  f g) h) (@comp_fapp0 (Functor_cat B C) W X Y (@one_cat_additive_family_add B C C1 Prod t A T0 X Y f
  (@one_cat_negative_family B C C1 Prod t A T0 X Y g)) h) (@one_cat_difference_family B C C1 Prod t A T0 W Y
  (@comp_fapp0 (Functor_cat B C) W X Y f h) (@comp_fapp0 (Functor_cat B C) W X Y g h)) (@eq_ap (@Transf B C X Y)
  (@Transf B C W Y) (λ k : τ (@Transf B C X Y), (@comp_fapp0 (Functor_cat B C) W X Y k h)) (@one_cat_difference_family
  B C C1 Prod t A T0 X Y f g) (@one_cat_additive_family_add B C C1 Prod t A T0 X Y f (@one_cat_negative_family B C C1
  Prod t A T0 X Y g)) (@one_cat_difference_family_formula_path B C C1 Prod t A T0 X Y f g)) (@eq_trans (@Transf B C W
  Y) (@comp_fapp0 (Functor_cat B C) W X Y (@one_cat_additive_family_add B C C1 Prod t A T0 X Y f
  (@one_cat_negative_family B C C1 Prod t A T0 X Y g)) h) (@one_cat_additive_family_add B C C1 Prod t A T0 W Y
  (@comp_fapp0 (Functor_cat B C) W X Y f h) (@comp_fapp0 (Functor_cat B C) W X Y (@one_cat_negative_family B C C1 Prod
  t A T0 X Y g) h)) (@one_cat_difference_family B C C1 Prod t A T0 W Y (@comp_fapp0 (Functor_cat B C) W X Y f h)
  (@comp_fapp0 (Functor_cat B C) W X Y g h)) (@one_cat_additive_family_precompose_path B C C1 Prod t A T0 W X Y
  f (@one_cat_negative_family B C C1 Prod t A T0 X Y g) h) (@eq_trans (@Transf B C W Y) (@one_cat_additive_family_add
  B C C1 Prod t A T0 W Y (@comp_fapp0 (Functor_cat B C) W X Y f h) (@comp_fapp0 (Functor_cat B C) W X Y
  (@one_cat_negative_family B C C1 Prod t A T0 X Y g) h)) (@one_cat_additive_family_add B C C1 Prod t A T0 W Y
  (@comp_fapp0 (Functor_cat B C) W X Y f h) (@one_cat_negative_family B C C1 Prod t A T0 W Y (@comp_fapp0 (Functor_cat
  B C) W X Y g h))) (@one_cat_difference_family B C C1 Prod t A T0 W Y (@comp_fapp0 (Functor_cat B C) W X Y f h)
  (@comp_fapp0 (Functor_cat B C) W X Y g h)) (@eq_ap (@Transf B C W Y) (@Transf B C W Y) (λ k : τ (@Transf B C W Y),
  (@one_cat_additive_family_add B C C1 Prod t A T0 W Y (@comp_fapp0 (Functor_cat B C) W X Y f h) k)) (@comp_fapp0
  (Functor_cat B C) W X Y (@one_cat_negative_family B C C1 Prod t A T0 X Y g) h) (@one_cat_negative_family B C C1 Prod
  t A T0 W Y (@comp_fapp0 (Functor_cat B C) W X Y g h)) (@eq_sym (@Transf B C W Y) (@one_cat_negative_family B C C1
  Prod t A T0 W Y (@comp_fapp0 (Functor_cat B C) W X Y g h)) (@comp_fapp0 (Functor_cat B C) W X Y
  (@one_cat_negative_family B C C1 Prod t A T0 X Y g) h) (@one_cat_negative_family_precompose_path B C C1 Prod t A T0
  W X Y h g))) (@eq_sym (@Transf B C W Y) (@one_cat_difference_family B C C1 Prod t A T0 W Y (@comp_fapp0 (Functor_cat
  B C) W X Y f h) (@comp_fapp0 (Functor_cat B C) W X Y g h)) (@one_cat_additive_family_add B C C1 Prod t A T0 W Y
  (@comp_fapp0 (Functor_cat B C) W X Y f h) (@one_cat_negative_family B C C1 Prod t A T0 W Y (@comp_fapp0 (Functor_cat
  B C) W X Y g h))) (@one_cat_difference_family_formula_path B C C1 Prod t A T0 W Y (@comp_fapp0 (Functor_cat B C) W X
  Y f h) (@comp_fapp0 (Functor_cat B C) W X Y g h))))));

// postcomposition preserves the original whole difference.
symbol one_cat_difference_family_postcompose_path [B C : Cat] (C1 : τ (IsNCat (cat_succ cat_zero) C)) [Prod : τ
  (Functor (Product_cat C C) C)] [t : τ (Obj C)] (A : τ (@AdditiveCategory C Prod t)) (T0 : τ (@TerminalObject (Op_cat
  C) t)) (X Y Z : τ (Functor B C)) (f g : τ (@Transf B C X Y)) (h : τ (@Transf B C Y Z))
  : τ (@= (@Transf B C X Z) (@comp_fapp0 (Functor_cat B C) X Y Z h (@one_cat_difference_family B C C1 Prod t A T0 X Y
  f g)) (@one_cat_difference_family B C C1 Prod t A T0 X Z (@comp_fapp0 (Functor_cat B C) X Y Z h f) (@comp_fapp0
  (Functor_cat B C) X Y Z h g)))
≔ (@eq_trans (@Transf B C X Z) (@comp_fapp0 (Functor_cat B C) X Y Z h (@one_cat_difference_family B C C1 Prod t A T0 X
  Y f g)) (@comp_fapp0 (Functor_cat B C) X Y Z h (@one_cat_additive_family_add B C C1 Prod t A T0 X Y f
  (@one_cat_negative_family B C C1 Prod t A T0 X Y g))) (@one_cat_difference_family B C C1 Prod t A T0 X Z
  (@comp_fapp0 (Functor_cat B C) X Y Z h f) (@comp_fapp0 (Functor_cat B C) X Y Z h g)) (@eq_ap (@Transf B C X Y)
  (@Transf B C X Z) (λ k : τ (@Transf B C X Y), (@comp_fapp0 (Functor_cat B C) X Y Z h k)) (@one_cat_difference_family
  B C C1 Prod t A T0 X Y f g) (@one_cat_additive_family_add B C C1 Prod t A T0 X Y f (@one_cat_negative_family B C C1
  Prod t A T0 X Y g)) (@one_cat_difference_family_formula_path B C C1 Prod t A T0 X Y f g)) (@eq_trans (@Transf B C X
  Z) (@comp_fapp0 (Functor_cat B C) X Y Z h (@one_cat_additive_family_add B C C1 Prod t A T0 X Y f
  (@one_cat_negative_family B C C1 Prod t A T0 X Y g))) (@one_cat_additive_family_add B C C1 Prod t A T0 X Z
  (@comp_fapp0 (Functor_cat B C) X Y Z h f) (@comp_fapp0 (Functor_cat B C) X Y Z h (@one_cat_negative_family B C C1
  Prod t A T0 X Y g))) (@one_cat_difference_family B C C1 Prod t A T0 X Z (@comp_fapp0 (Functor_cat B C) X Y Z h f)
  (@comp_fapp0 (Functor_cat B C) X Y Z h g)) (@one_cat_additive_family_postcompose_path B C C1 Prod t A T0 X Y Z
  f (@one_cat_negative_family B C C1 Prod t A T0 X Y g) h) (@eq_trans (@Transf B C X Z) (@one_cat_additive_family_add
  B C C1 Prod t A T0 X Z (@comp_fapp0 (Functor_cat B C) X Y Z h f) (@comp_fapp0 (Functor_cat B C) X Y Z h
  (@one_cat_negative_family B C C1 Prod t A T0 X Y g))) (@one_cat_additive_family_add B C C1 Prod t A T0 X Z
  (@comp_fapp0 (Functor_cat B C) X Y Z h f) (@one_cat_negative_family B C C1 Prod t A T0 X Z (@comp_fapp0 (Functor_cat
  B C) X Y Z h g))) (@one_cat_difference_family B C C1 Prod t A T0 X Z (@comp_fapp0 (Functor_cat B C) X Y Z h f)
  (@comp_fapp0 (Functor_cat B C) X Y Z h g)) (@eq_ap (@Transf B C X Z) (@Transf B C X Z) (λ k : τ (@Transf B C X Z),
  (@one_cat_additive_family_add B C C1 Prod t A T0 X Z (@comp_fapp0 (Functor_cat B C) X Y Z h f) k)) (@comp_fapp0
  (Functor_cat B C) X Y Z h (@one_cat_negative_family B C C1 Prod t A T0 X Y g)) (@one_cat_negative_family B C C1 Prod
  t A T0 X Z (@comp_fapp0 (Functor_cat B C) X Y Z h g)) (@eq_sym (@Transf B C X Z) (@one_cat_negative_family B C C1
  Prod t A T0 X Z (@comp_fapp0 (Functor_cat B C) X Y Z h g)) (@comp_fapp0 (Functor_cat B C) X Y Z h
  (@one_cat_negative_family B C C1 Prod t A T0 X Y g)) (@one_cat_negative_family_postcompose_path B C C1 Prod t A T0 X
  Y Z g h))) (@eq_sym (@Transf B C X Z) (@one_cat_difference_family B C C1 Prod t A T0 X Z (@comp_fapp0 (Functor_cat B
  C) X Y Z h f) (@comp_fapp0 (Functor_cat B C) X Y Z h g)) (@one_cat_additive_family_add B C C1 Prod t A T0 X Z
  (@comp_fapp0 (Functor_cat B C) X Y Z h f) (@one_cat_negative_family B C C1 Prod t A T0 X Z (@comp_fapp0 (Functor_cat
  B C) X Y Z h g))) (@one_cat_difference_family_formula_path B C C1 Prod t A T0 X Z (@comp_fapp0 (Functor_cat B C) X Y
  Z h f) (@comp_fapp0 (Functor_cat B C) X Y Z h g))))));
