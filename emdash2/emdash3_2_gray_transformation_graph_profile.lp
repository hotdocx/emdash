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

// Object observation is ordinary action of the whole carrier path.
symbol strict_gray_transf_graph_obj_path
  [B C : Cat]
  (SF SG : τ (@StrictFunctorData B C))
  (epsilon : τ (Transf
    (@strict_functor_carrier B C SF)
    (@strict_functor_carrier B C SG)))
  (x : τ (Obj B))
  : τ (@=
      (Obj (@LaxArrow_cat C))
      (@fapp0
        B (@LaxArrow_cat C)
        (@strict_functor_carrier
          B (@LaxArrow_cat C)
          (@strict_gray_transf_graph_data B C SF SG epsilon))
        x)
      (@gray_transf_graph_obj
        B C
        (@strict_functor_carrier B C SF)
        (@strict_functor_carrier B C SG)
        epsilon x))
≔ @eq_ap
    (Functor B (@LaxArrow_cat C))
    (Obj (@LaxArrow_cat C))
    (λ H : τ (Functor B (@LaxArrow_cat C)),
      @fapp0 B (@LaxArrow_cat C) H x)
    (@strict_functor_carrier
      B (@LaxArrow_cat C)
      (@strict_gray_transf_graph_data B C SF SG epsilon))
    (@gray_transf_graph_func
      B C
      (@strict_functor_carrier B C SF)
      (@strict_functor_carrier B C SG)
      epsilon)
    (@strict_gray_transf_graph_carrier_path B C SF SG epsilon);

// Arrow observation is necessarily dependent because its two endpoint objects
// vary with the functor.  `eq_apd` preserves that exact dependency rather than
// forcing a false equality in one fixed Hom category.
symbol strict_gray_transf_graph_arrow_pathover
  [B C : Cat]
  (SF SG : τ (@StrictFunctorData B C))
  (epsilon : τ (Transf
    (@strict_functor_carrier B C SF)
    (@strict_functor_carrier B C SG)))
  [x y : τ (Obj B)]
  (g : τ (Hom B x y))
  : τ (@PathOver
      (Functor B (@LaxArrow_cat C))
      (λ H : τ (Functor B (@LaxArrow_cat C)),
        @Hom
          (@LaxArrow_cat C)
          (@fapp0 B (@LaxArrow_cat C) H x)
          (@fapp0 B (@LaxArrow_cat C) H y))
      (@strict_functor_carrier
        B (@LaxArrow_cat C)
        (@strict_gray_transf_graph_data B C SF SG epsilon))
      (@gray_transf_graph_func
        B C
        (@strict_functor_carrier B C SF)
        (@strict_functor_carrier B C SG)
        epsilon)
      (@strict_gray_transf_graph_carrier_path B C SF SG epsilon)
      (@fapp1_fapp0
        B (@LaxArrow_cat C)
        (@strict_functor_carrier
          B (@LaxArrow_cat C)
          (@strict_gray_transf_graph_data B C SF SG epsilon))
        x y g)
      (@gray_transf_graph_arrow
        B C
        (@strict_functor_carrier B C SF)
        (@strict_functor_carrier B C SG)
        epsilon x y g))
≔ @eq_apd
    (Functor B (@LaxArrow_cat C))
    (λ H : τ (Functor B (@LaxArrow_cat C)),
      @Hom
        (@LaxArrow_cat C)
        (@fapp0 B (@LaxArrow_cat C) H x)
        (@fapp0 B (@LaxArrow_cat C) H y))
    (λ H : τ (Functor B (@LaxArrow_cat C)),
      @fapp1_fapp0 B (@LaxArrow_cat C) H x y g)
    (@strict_functor_carrier
      B (@LaxArrow_cat C)
      (@strict_gray_transf_graph_data B C SF SG epsilon))
    (@gray_transf_graph_func
      B C
      (@strict_functor_carrier B C SF)
      (@strict_functor_carrier B C SG)
      epsilon)
    (@strict_gray_transf_graph_carrier_path B C SF SG epsilon);
