require open emdash.emdash3_2;
symbol one_cat_op [C : Cat] (C1 : τ (IsNCat (cat_succ cat_zero) C))
  : τ (IsNCat (cat_succ cat_zero) (Op_cat C))
≔ λ x : τ (Obj (Op_cat C)), λ y : τ (Obj (Op_cat C)), C1 y x;
