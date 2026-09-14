require open emdash.emdash3_2_one_cat_additive_family_units;

// Whole addition has its original zero as a right unit.
assert [B C : Cat] (C1 : τ (IsNCat (cat_succ cat_zero) C)) [Prod : τ (Functor (Product_cat C C) C)] [t : τ (Obj
  C)] (A : τ (@AdditiveCategory C Prod t)) (T0 : τ (@TerminalObject (Op_cat C) t)) (X Y : τ (Functor B C)) (f : τ
  (@Transf B C X Y)) ⊢ @one_cat_additive_family_right_zero_path B C C1 Prod t A T0 X Y f : τ (@= (@Transf B C X Y)
  (@one_cat_additive_family_add B C C1 Prod t A T0 X Y f (@zero_arrow_family_zero_transf B C t
  (@additive_terminal_object C Prod t A) T0 X Y)) f);
assert [B C : Cat] (C1 : τ (IsNCat (cat_succ cat_zero) C)) [Prod : τ (Functor (Product_cat C C) C)] [t : τ (Obj
  C)] (A : τ (@AdditiveCategory C Prod t)) (T0 : τ (@TerminalObject (Op_cat C) t)) (X Y : τ (Functor B C)) ⊢
  @one_cat_negative_family_zero_path B C C1 Prod t A T0 X Y : τ (@= (@Transf B C X Y) (@one_cat_negative_family B
  C C1 Prod t A T0 X Y (@zero_arrow_family_zero_transf B C t (@additive_terminal_object C Prod t A) T0 X Y))
  (@zero_arrow_family_zero_transf B C t (@additive_terminal_object C Prod t A) T0 X Y));
assert [B C : Cat] (C1 : τ (IsNCat (cat_succ cat_zero) C)) [Prod : τ (Functor (Product_cat C C) C)] [t : τ (Obj
  C)] (A : τ (@AdditiveCategory C Prod t)) (T0 : τ (@TerminalObject (Op_cat C) t)) (X Y : τ (Functor B C)) (f : τ
  (@Transf B C X Y)) ⊢ @one_cat_difference_family_right_zero_path B C C1 Prod t A T0 X Y f : τ (@= (@Transf B C X
  Y) (@one_cat_difference_family B C C1 Prod t A T0 X Y f (@zero_arrow_family_zero_transf B C t
  (@additive_terminal_object C Prod t A) T0 X Y)) f);

// The preserved-class law uses the supplied annihilation of the actual correction.
assert [B C : Cat] (C1 : τ (IsNCat (cat_succ cat_zero) C)) [Prod : τ (Functor (Product_cat C C) C)] [t : τ (Obj
  C)] (A : τ (@AdditiveCategory C Prod t)) (T0 : τ (@TerminalObject (Op_cat C) t)) (X Y : τ (Functor B C)) (Z : τ
  (Functor B C)) (f g : τ (@Transf B C X Y)) (h : τ (@Transf B C Y Z)) (e : τ (@= (@Transf B C X Z) (@comp_fapp0
  (Functor_cat B C) X Y Z h g) (@zero_arrow_family_zero_transf B C t (@additive_terminal_object C Prod t A) T0 X
  Z))) ⊢ @one_cat_difference_killed_second_path B C C1 Prod t A T0 X Y Z f g h e : τ (@= (@Transf B C X Z)
  (@comp_fapp0 (Functor_cat B C) X Y Z h (@one_cat_difference_family B C C1 Prod t A T0 X Y f g)) (@comp_fapp0
  (Functor_cat B C) X Y Z h f));
assertnot [B C : Cat] (C1 : τ (IsNCat (cat_succ cat_zero) C)) [Prod : τ (Functor (Product_cat C C) C)] [t : τ (Obj
  C)] (A : τ (@AdditiveCategory C Prod t)) (T0 : τ (@TerminalObject (Op_cat C) t)) (X Y : τ (Functor B C)) (f : τ
  (@Transf B C X Y)) (other : τ (@Transf B C X Y)) ⊢ @one_cat_difference_family_right_zero_path B C C1 Prod t A T0
  X Y f : τ (@= (@Transf B C X Y) (@one_cat_difference_family B C C1 Prod t A T0 X Y f
  (@zero_arrow_family_zero_transf B C t (@additive_terminal_object C Prod t A) T0 X Y)) other);
