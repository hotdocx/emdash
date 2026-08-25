/*
  Emdash v3.2: selected strict-profile closure of transformation graphs.

  If F and G already have StrictFunctorData codes, then a transformation
  epsilon:F=>G has a selected strict graph code

    B -> LaxArrow_cat(C).

  A whole carrier path identifies its stable strict decoder with the
  transparent graph from the preceding module.  Keeping the decoder head
  stable lets the existing strict compositor rule compute before readability
  reframes it to the graph. This is the profile closure needed by recursive
  Gray currying; it does not classify arbitrary ambient graphs as strict,
  identify the retained target side with a separately named G[g], or add a
  second graph semantics.
*/

require open emdash.emdash3_2_gray_cubes;

// Transformation graphs preserve the selected strict endpoint profile.
injective symbol strict_gray_transf_graph_data
  [B C : Cat]
  (SF SG : τ (@StrictFunctorData B C))
  (epsilon : τ (Transf
    (@strict_functor_carrier B C SF)
    (@strict_functor_carrier B C SG)))
  : τ (@StrictFunctorData B (@LaxArrow_cat C));

// Whole readability boundary. This is equality evidence, not a carrier fold:
// the stable strict-code head remains available to profile-local computation.
constant symbol strict_gray_transf_graph_carrier_path
  [B C : Cat]
  (SF SG : τ (@StrictFunctorData B C))
  (epsilon : τ (Transf
    (@strict_functor_carrier B C SF)
    (@strict_functor_carrier B C SG)))
  : τ (@=
      (Functor B (@LaxArrow_cat C))
      (@strict_functor_carrier
        B (@LaxArrow_cat C)
        (@strict_gray_transf_graph_data B C SF SG epsilon))
      (@gray_transf_graph_func
        B C
        (@strict_functor_carrier B C SF)
        (@strict_functor_carrier B C SG)
        epsilon));
