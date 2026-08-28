/*
  Emdash v3.2: selected strict-profile closure of transformation graphs.

  If F and G carry IsStrictFunctor evidence, then a transformation
  epsilon:F=>G has a selected strict graph package

    B -> LaxArrow_cat(C).

  Its underlying functor is the public graph from the preceding module and a
  supplied property certifies the existing compositor. This is the strictness
  closure needed by recursive Gray currying; it does not add a second graph
  semantics or reflect semantic evidence into a judgmental cell. The existing IsPseudoFunctor is a separate
  fixed-forward OmegaEquivAlong capability indexed by an already-formed
  carrier.
*/

require open emdash.emdash3_2_gray_cubes;

// Supplied strictness closure for the already-existing transformation graph.
constant symbol gray_transf_graph_is_strict
  [B C : Cat]
  (SF SG : τ (@StrictFunctor B C))
  (epsilon : τ (Transf
    (@strict_functor B C SF)
    (@strict_functor B C SG)))
  : τ (@IsStrictFunctor
      B
      (@LaxArrow_cat C)
      (@gray_transf_graph_func
        B C
        (@strict_functor B C SF)
        (@strict_functor B C SG)
        epsilon));

symbol strict_gray_transf_graph
  [B C : Cat]
  (SF SG : τ (@StrictFunctor B C))
  (epsilon : τ (Transf
    (@strict_functor B C SF)
    (@strict_functor B C SG)))
  : τ (@StrictFunctor B (@LaxArrow_cat C))
≔ @strict_functor_intro
    B
    (@LaxArrow_cat C)
    (@gray_transf_graph_func
      B C
      (@strict_functor B C SF)
      (@strict_functor B C SG)
      epsilon)
    (@gray_transf_graph_is_strict B C SF SG epsilon);
