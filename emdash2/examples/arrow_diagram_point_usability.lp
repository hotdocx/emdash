require open emdash.emdash3_2_one_cat_arrow_diagrams;

assert [K C : Cat] (F G : τ (Functor K C))
  (eta : τ (@Transf K C F G)) (x : τ (Obj K)) ⊢
  @eq_refl (Functor WalkingArrow_cat C)
    (@fapp0 K (Functor_cat WalkingArrow_cat C)
      (@transf_arrow_diagram_func K C F G eta) x)
  : τ (@= (Functor WalkingArrow_cat C)
      (@fapp0 K (Functor_cat WalkingArrow_cat C)
        (@transf_arrow_diagram_func K C F G eta) x)
      (@walking_arrow_func C (@fapp0 K C F x) (@fapp0 K C G x)
        (@tapp0_fapp0 K C F G x eta)));

assert [C : Cat] (C1 : τ (IsNCat (cat_succ cat_zero) C))
  [X Y : τ (Obj C)] (u : τ (Hom C X Y)) ⊢
  @eq_refl (Functor WalkingArrow_cat C)
    (@fapp0 (@LaxArrow_cat C) (Functor_cat WalkingArrow_cat C)
      (@one_cat_arrow_diagram_func C C1) (@lax_edge C X Y u))
  : τ (@= (Functor WalkingArrow_cat C)
      (@fapp0 (@LaxArrow_cat C) (Functor_cat WalkingArrow_cat C)
        (@one_cat_arrow_diagram_func C C1) (@lax_edge C X Y u))
      (@walking_arrow_func C X Y u));

assertnot [K C : Cat] (F G : τ (Functor K C))
  (eta : τ (@Transf K C F G)) (x : τ (Obj K))
  (other : τ (Hom C (@fapp0 K C F x) (@fapp0 K C G x))) ⊢
  @eq_refl (Functor WalkingArrow_cat C)
    (@fapp0 K (Functor_cat WalkingArrow_cat C)
      (@transf_arrow_diagram_func K C F G eta) x)
  : τ (@= (Functor WalkingArrow_cat C)
      (@fapp0 K (Functor_cat WalkingArrow_cat C)
        (@transf_arrow_diagram_func K C F G eta) x)
      (@walking_arrow_func C (@fapp0 K C F x) (@fapp0 K C G x) other));
