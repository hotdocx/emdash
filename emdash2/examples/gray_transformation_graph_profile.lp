/*
  Reviewer example: the whole transformation graph closes the selected strict
  functor property when both endpoint diagrams already carry strictness
  evidence.
*/

require open emdash.emdash3_2_gray_transformation_graph_profile;

// The strict package has the public graph as its underlying carrier.
assert [B C : Cat]
  (SF SG : τ (@StrictFunctor B C))
  (epsilon : τ (Transf
    (@strict_functor B C SF)
    (@strict_functor B C SG))) ⊢
  @strict_functor_underlying
    B (@LaxArrow_cat C)
    (@strict_gray_transf_graph B C SF SG epsilon)
  ≡ @gray_transf_graph_func
      B C
      (@strict_functor B C SF)
      (@strict_functor B C SG)
      epsilon;

assert [B C : Cat]
  (SF SG : τ (@StrictFunctor B C))
  (epsilon : τ (Transf
    (@strict_functor B C SF)
    (@strict_functor B C SG)))
  (x : τ (Obj B)) ⊢
  @fapp0
    B (@LaxArrow_cat C)
    (@strict_functor
      B (@LaxArrow_cat C)
      (@strict_gray_transf_graph B C SF SG epsilon))
    x
  ≡ @gray_transf_graph_obj
      B C
      (@strict_functor B C SF)
      (@strict_functor B C SG)
      epsilon x;

assert [B C : Cat]
  (SF SG : τ (@StrictFunctor B C))
  (epsilon : τ (Transf
    (@strict_functor B C SF)
    (@strict_functor B C SG)))
  [x y : τ (Obj B)]
  (g : τ (Hom B x y)) ⊢
  @fapp1_fapp0
    B (@LaxArrow_cat C)
    (@strict_functor
      B (@LaxArrow_cat C)
      (@strict_gray_transf_graph B C SF SG epsilon))
    x y g
  ≡ @gray_transf_graph_arrow
      B C
      (@strict_functor B C SF)
      (@strict_functor B C SG)
      epsilon x y g;

// The package retains the supplied property over the existing graph
// compositor; no graph-specific unit or compositor cell is introduced.
assert [B C : Cat]
  (SF SG : τ (@StrictFunctor B C))
  (epsilon : τ (Transf
    (@strict_functor B C SF)
    (@strict_functor B C SG)))
  ⊢
  @strict_functor_evidence
    B (@LaxArrow_cat C)
    (@strict_gray_transf_graph B C SF SG epsilon)
  ≡ @gray_transf_graph_is_strict B C SF SG epsilon;
