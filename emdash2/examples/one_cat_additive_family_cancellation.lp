/* Categorical whole cancellation without a supplied additive capability on Functor_cat. */
require open emdash.emdash3_2_one_cat_additive_family_cancellation;

assert [B C : Cat] (C1 : τ (IsNCat (cat_succ cat_zero) C)) [Prod : τ (Functor (Product_cat C C) C)] [t : τ (Obj C)] (V
  : τ (@AdditiveCategory C Prod t)) (T0 : τ (@TerminalObject (Op_cat C) t)) (X Y : τ (Functor B C)) (a b c : τ
  (@Transf B C X Y)) (p : τ (@= (@Transf B C X Y) (@one_cat_additive_family_add B C C1 Prod t V T0 X Y a b)
  (@one_cat_additive_family_add B C C1 Prod t V T0 X Y a c))) ⊢ @one_cat_additive_family_left_cancel B C C1 Prod t V
  T0 X Y a b c p : τ (@= (@Transf B C X Y) b c);
assert [B C : Cat] (C1 : τ (IsNCat (cat_succ cat_zero) C)) [Prod : τ (Functor (Product_cat C C) C)] [t : τ (Obj C)] (V
  : τ (@AdditiveCategory C Prod t)) (T0 : τ (@TerminalObject (Op_cat C) t)) (X Y : τ (Functor B C)) (f g : τ (@Transf
  B C X Y)) (p : τ (@= (@Transf B C X Y) (@one_cat_negative_family B C C1 Prod t V T0 X Y f) (@one_cat_negative_family
  B C C1 Prod t V T0 X Y g))) ⊢ @one_cat_negative_family_reflect_path B C C1 Prod t V T0 X Y f g p : τ (@= (@Transf B
  C X Y) f g);
assert [B C : Cat] (C1 : τ (IsNCat (cat_succ cat_zero) C)) [Prod : τ (Functor (Product_cat C C) C)] [t : τ (Obj C)] (V
  : τ (@AdditiveCategory C Prod t)) (T0 : τ (@TerminalObject (Op_cat C) t)) (X Y : τ (Functor B C)) (f g : τ (@Transf
  B C X Y)) (p : τ (@= (@Transf B C X Y) (@one_cat_difference_family B C C1 Prod t V T0 X Y f g)
  (@zero_arrow_family_zero_transf B C t (@additive_terminal_object C Prod t V) T0 X Y))) ⊢
  @one_cat_difference_family_zero_reflect B C C1 Prod t V T0 X Y f g p : τ (@= (@Transf B C X Y) f g);
assert [B C : Cat] (C1 : τ (IsNCat (cat_succ cat_zero) C)) [Prod : τ (Functor (Product_cat C C) C)] [t : τ (Obj C)] (V
  : τ (@AdditiveCategory C Prod t)) (T0 : τ (@TerminalObject (Op_cat C) t)) (X Y : τ (Functor B C)) (f g : τ (@Transf
  B C X Y)) (p : τ (@= (@Transf B C X Y) f g)) ⊢ @one_cat_difference_family_precompose_zero_path B C C1 Prod t V T0 X
  X Y f g (@id (Functor_cat B C) X) p : τ (@= (@Transf B C X Y) (@one_cat_difference_family B C C1 Prod t V T0 X Y f
  g) (@zero_arrow_family_zero_transf B C t (@additive_terminal_object C Prod t V) T0 X Y));
assert [B C : Cat] (C1 : τ (IsNCat (cat_succ cat_zero) C)) [Prod : τ (Functor (Product_cat C C) C)] [t : τ (Obj C)] (V
  : τ (@AdditiveCategory C Prod t)) (T0 : τ (@TerminalObject (Op_cat C) t)) (W X Y : τ (Functor B C)) (f g : τ
  (@Transf B C X Y)) (h : τ (@Transf B C W X)) (p : τ (@= (@Transf B C W Y) (@comp_fapp0 (Functor_cat B C) W X Y f h)
  (@comp_fapp0 (Functor_cat B C) W X Y g h))) ⊢ @one_cat_difference_family_precompose_zero_path B C C1 Prod t V T0 W X
  Y f g h p : τ (@= (@Transf B C W Y) (@comp_fapp0 (Functor_cat B C) W X Y (@one_cat_difference_family B C C1 Prod t V
  T0 X Y f g) h) (@zero_arrow_family_zero_transf B C t (@additive_terminal_object C Prod t V) T0 W Y));
assert [B C : Cat] (C1 : τ (IsNCat (cat_succ cat_zero) C)) [Prod : τ (Functor (Product_cat C C) C)] [t : τ (Obj C)] (V
  : τ (@AdditiveCategory C Prod t)) (T0 : τ (@TerminalObject (Op_cat C) t)) (X Y Z : τ (Functor B C)) (f g : τ
  (@Transf B C X Y)) (h : τ (@Transf B C Y Z)) (p : τ (@= (@Transf B C X Z) (@comp_fapp0 (Functor_cat B C) X Y Z h f)
  (@comp_fapp0 (Functor_cat B C) X Y Z h g))) ⊢ @one_cat_difference_family_postcompose_zero_path B C C1 Prod t V T0 X
  Y Z f g h p : τ (@= (@Transf B C X Z) (@comp_fapp0 (Functor_cat B C) X Y Z h (@one_cat_difference_family B C C1 Prod
  t V T0 X Y f g)) (@zero_arrow_family_zero_transf B C t (@additive_terminal_object C Prod t V) T0 X Z));
assertnot [B C : Cat] (C1 : τ (IsNCat (cat_succ cat_zero) C)) [Prod : τ (Functor (Product_cat C C) C)] [t : τ (Obj C)]
  (V : τ (@AdditiveCategory C Prod t)) (T0 : τ (@TerminalObject (Op_cat C) t)) (X Y : τ (Functor B C)) (a b c : τ
  (@Transf B C X Y)) ⊢ @eq_refl (@Transf B C X Y) (@one_cat_additive_family_add B C C1 Prod t V T0 X Y a b) : τ (@=
  (@Transf B C X Y) (@one_cat_additive_family_add B C C1 Prod t V T0 X Y a b) (@one_cat_additive_family_add B C C1
  Prod t V T0 X Y a c));
