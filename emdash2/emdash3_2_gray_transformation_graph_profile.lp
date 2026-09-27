/*
  Emdash v3.2: selected strict-profile closure of transformation graphs.

  If F and G carry IsStrictFunctor evidence, then one classified lax transfor
  between them has a selected strict graph package

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
  (L : τ (@LaxTransfor
    B C
    (@strict_functor B C SF)
    (@strict_functor B C SG)))
  : τ (@IsStrictFunctor
      B
      (@LaxArrow_cat C)
      (@gray_transf_graph_func
        B C
        (@strict_functor B C SF)
        (@strict_functor B C SG)
        L));

symbol strict_gray_transf_graph
  [B C : Cat]
  (SF SG : τ (@StrictFunctor B C))
  (L : τ (@LaxTransfor
    B C
    (@strict_functor B C SF)
    (@strict_functor B C SG)))
  : τ (@StrictFunctor B (@LaxArrow_cat C))
≔ @make_strict_functor
    B
    (@LaxArrow_cat C)
    (@gray_transf_graph_func
      B C
      (@strict_functor B C SF)
      (@strict_functor B C SG)
      L)
    (@gray_transf_graph_is_strict B C SF SG L);
