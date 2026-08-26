/*
  Reviewer example: the whole transformation graph closes the selected strict
  functor-code profile when both endpoint diagrams are already strict-coded.
*/

require open emdash.emdash3_2_gray_transformation_graph_profile;

// The strict code decodes judgmentally to the public graph.
assert [B C : Cat]
  (SF SG : τ (@StrictFunctorData B C))
  (epsilon : τ (Transf
    (@strict_functor_carrier B C SF)
    (@strict_functor_carrier B C SG))) ⊢
  @strict_functor_carrier
    B (@LaxArrow_cat C)
    (@strict_gray_transf_graph_data B C SF SG epsilon)
  ≡ @gray_transf_graph_func
      B C
      (@strict_functor_carrier B C SF)
      (@strict_functor_carrier B C SG)
      epsilon;

assert [B C : Cat]
  (SF SG : τ (@StrictFunctorData B C))
  (epsilon : τ (Transf
    (@strict_functor_carrier B C SF)
    (@strict_functor_carrier B C SG)))
  (x : τ (Obj B)) ⊢
  @fapp0
    B (@LaxArrow_cat C)
    (@strict_functor_carrier
      B (@LaxArrow_cat C)
      (@strict_gray_transf_graph_data B C SF SG epsilon))
    x
  ≡ @gray_transf_graph_obj
      B C
      (@strict_functor_carrier B C SF)
      (@strict_functor_carrier B C SG)
      epsilon x;

assert [B C : Cat]
  (SF SG : τ (@StrictFunctorData B C))
  (epsilon : τ (Transf
    (@strict_functor_carrier B C SF)
    (@strict_functor_carrier B C SG)))
  [x y : τ (Obj B)]
  (g : τ (Hom B x y)) ⊢
  @fapp1_fapp0
    B (@LaxArrow_cat C)
    (@strict_functor_carrier
      B (@LaxArrow_cat C)
      (@strict_gray_transf_graph_data B C SF SG epsilon))
    x y g
  ≡ @gray_transf_graph_arrow
      B C
      (@strict_functor_carrier B C SF)
      (@strict_functor_carrier B C SG)
      epsilon x y g;

// The selected code activates the existing profile-local compositor beta.
assert [B C : Cat]
  (SF SG : τ (@StrictFunctorData B C))
  (epsilon : τ (Transf
    (@strict_functor_carrier B C SF)
    (@strict_functor_carrier B C SG)))
  [X Y Z : τ (Obj B)]
  (g : τ (Hom B Y Z))
  (f : τ (Hom B X Y)) ⊢
  @fapp1_compositor
    B
    (@LaxArrow_cat C)
    (@strict_functor_carrier
      B (@LaxArrow_cat C)
      (@strict_gray_transf_graph_data B C SF SG epsilon))
    X Y Z g f
  ≡ @id
      (Hom_cat
        (@LaxArrow_cat C)
        (@fapp0
          B (@LaxArrow_cat C)
          (@strict_functor_carrier
            B (@LaxArrow_cat C)
            (@strict_gray_transf_graph_data B C SF SG epsilon))
          X)
        (@fapp0
          B (@LaxArrow_cat C)
          (@strict_functor_carrier
            B (@LaxArrow_cat C)
            (@strict_gray_transf_graph_data B C SF SG epsilon))
          Z))
      (@strict_functor_compositor_lhs
        B
        (@LaxArrow_cat C)
        (@strict_functor_carrier
          B (@LaxArrow_cat C)
          (@strict_gray_transf_graph_data B C SF SG epsilon))
        X Y Z g f);
