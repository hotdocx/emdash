/*
  An ordinary arrow, presented as a functor out of the existing walking arrow.

  The join cross datum is a constant section of a represented Hom family,
  not a new primitive arrow or a supplied commuting square. Ordinary
  generator action computes by the join recursor's whole cross beta.
  This module does not yet internalize variation of the supplied arrow and
  both endpoints into a whole inverse to diagram evaluation.
*/
require open emdash.emdash3_2_walking_arrow;

// Transparent internally natural cross datum selecting f at the terminal pair.
symbol walking_arrow_cross
  [C : Cat] [x y : τ (Obj C)] (f : τ (Hom C x y))
  : τ (Obj (@Prof_transf_cat
      C Terminal_cat C Terminal_cat
      (@Terminal_prof Terminal_cat Terminal_cat)
      (@Obj_func C x) (@Unit_prof C) (@Obj_func C y)))
≔ @Const_func (Product_cat (Op_cat Terminal_cat) Terminal_cat)
    (Hom_cat C x y) f;

// Transparent join-recursion introduction: [1] → C, sending 0→1 to f.
symbol walking_arrow_func
  [C : Cat] [x y : τ (Obj C)] (f : τ (Hom C x y))
  : τ (Functor WalkingArrow_cat C)
≔ @join_elim_func Terminal_cat Terminal_cat C
    (@Obj_func C x) (@Obj_func C y) (@walking_arrow_cross C x y f);
