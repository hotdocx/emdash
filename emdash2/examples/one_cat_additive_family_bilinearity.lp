/* Whole additive and subtractive bilinearity at the retained functors. */
require open emdash.emdash3_2_one_cat_difference_family_bilinearity;

assert [B C : Cat] (C1 : τ (IsNCat (cat_succ cat_zero) C)) [Prod : τ (Functor (Product_cat C C) C)] [t : τ (Obj C)] (A
  : τ (@AdditiveCategory C Prod t)) (T0 : τ (@TerminalObject (Op_cat C) t)) (W X Y : τ (Functor B C)) (f g : τ
  (@Transf B C X Y)) (h : τ (@Transf B C W X)) ⊢ @one_cat_additive_family_precompose_path B C C1 Prod t A T0 W X Y f g
  h : τ (@= (@Transf B C W Y) (@comp_fapp0 (Functor_cat B C) W X Y (@one_cat_additive_family_add B C C1 Prod t A T0 X
  Y f g) h) (@one_cat_additive_family_add B C C1 Prod t A T0 W Y (@comp_fapp0 (Functor_cat B C) W X Y f h)
  (@comp_fapp0 (Functor_cat B C) W X Y g h)));
assert [B C : Cat] (C1 : τ (IsNCat (cat_succ cat_zero) C)) [Prod : τ (Functor (Product_cat C C) C)] [t : τ (Obj C)] (A
  : τ (@AdditiveCategory C Prod t)) (T0 : τ (@TerminalObject (Op_cat C) t)) (X Y Z : τ (Functor B C)) (f g : τ
  (@Transf B C X Y)) (h : τ (@Transf B C Y Z)) ⊢ @one_cat_additive_family_postcompose_path B C C1 Prod t A T0 X Y Z f
  g h : τ (@= (@Transf B C X Z) (@comp_fapp0 (Functor_cat B C) X Y Z h (@one_cat_additive_family_add B C C1 Prod t A
  T0 X Y f g)) (@one_cat_additive_family_add B C C1 Prod t A T0 X Z (@comp_fapp0 (Functor_cat B C) X Y Z h f)
  (@comp_fapp0 (Functor_cat B C) X Y Z h g)));
assert [B C : Cat] (C1 : τ (IsNCat (cat_succ cat_zero) C)) [Prod : τ (Functor (Product_cat C C) C)] [t : τ (Obj C)] (A
  : τ (@AdditiveCategory C Prod t)) (T0 : τ (@TerminalObject (Op_cat C) t)) (X Y Z : τ (Functor B C)) (f g : τ
  (@Transf B C X Y)) (h : τ (@Transf B C Y Z)) (i j : τ (Obj B)) (u : τ (Hom B i j)) ⊢ @eq_ap (@Transf B C X Z) (Hom C
  (@fapp0 B C X i) (@fapp0 B C Z j)) (λ k : τ (@Transf B C X Z), @tapp1_fapp0 B C X Z i j k u) (@comp_fapp0
  (Functor_cat B C) X Y Z h (@one_cat_additive_family_add B C C1 Prod t A T0 X Y f g)) (@one_cat_additive_family_add B
  C C1 Prod t A T0 X Z (@comp_fapp0 (Functor_cat B C) X Y Z h f) (@comp_fapp0 (Functor_cat B C) X Y Z h g))
  (@one_cat_additive_family_postcompose_path B C C1 Prod t A T0 X Y Z f g h) : τ (@= (Hom C (@fapp0 B C X i) (@fapp0 B
  C Z j)) (@tapp1_fapp0 B C X Z i j (@comp_fapp0 (Functor_cat B C) X Y Z h (@one_cat_additive_family_add B C C1 Prod t
  A T0 X Y f g)) u) (@tapp1_fapp0 B C X Z i j (@one_cat_additive_family_add B C C1 Prod t A T0 X Z (@comp_fapp0
  (Functor_cat B C) X Y Z h f) (@comp_fapp0 (Functor_cat B C) X Y Z h g)) u));
assert [B C : Cat] (C1 : τ (IsNCat (cat_succ cat_zero) C)) [Prod : τ (Functor (Product_cat C C) C)] [t : τ (Obj C)] (A
  : τ (@AdditiveCategory C Prod t)) (T0 : τ (@TerminalObject (Op_cat C) t)) (W X Y : τ (Functor B C)) (f g : τ
  (@Transf B C X Y)) (h : τ (@Transf B C W X)) ⊢ @one_cat_difference_family_precompose_path B C C1 Prod t A T0 W X Y f
  g h : τ (@= (@Transf B C W Y) (@comp_fapp0 (Functor_cat B C) W X Y (@one_cat_difference_family B C C1 Prod t A T0 X
  Y f g) h) (@one_cat_difference_family B C C1 Prod t A T0 W Y (@comp_fapp0 (Functor_cat B C) W X Y f h) (@comp_fapp0
  (Functor_cat B C) W X Y g h)));
assert [B C : Cat] (C1 : τ (IsNCat (cat_succ cat_zero) C)) [Prod : τ (Functor (Product_cat C C) C)] [t : τ (Obj C)] (A
  : τ (@AdditiveCategory C Prod t)) (T0 : τ (@TerminalObject (Op_cat C) t)) (X Y Z : τ (Functor B C)) (f g : τ
  (@Transf B C X Y)) (h : τ (@Transf B C Y Z)) ⊢ @one_cat_difference_family_postcompose_path B C C1 Prod t A T0 X Y Z
  f g h : τ (@= (@Transf B C X Z) (@comp_fapp0 (Functor_cat B C) X Y Z h (@one_cat_difference_family B C C1 Prod t A
  T0 X Y f g)) (@one_cat_difference_family B C C1 Prod t A T0 X Z (@comp_fapp0 (Functor_cat B C) X Y Z h f)
  (@comp_fapp0 (Functor_cat B C) X Y Z h g)));
