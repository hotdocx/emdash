/*
  Reviewer example: a classified lax transfor between strict endpoint
  diagrams has one selected strict graph package.
*/

require open emdash.emdash3_2_gray_transformation_graph_profile;

// The explicit raw graph observation computes through hom action; the stable
// strict view checked below deliberately remains at runtime.
assert [B C : Cat]
  (SF SG : τ (@StrictFunctor B C))
  (L : τ (@LaxTransfor
    B C
    (@strict_functor B C SF)
    (@strict_functor B C SG)))
  [x y : τ (Obj B)]
  (g : τ (Hom B x y)) ⊢
  @fapp1_fapp0
    B (@LaxArrow_cat C)
    (@strict_functor_underlying
      B (@LaxArrow_cat C)
      (@strict_gray_transf_graph B C SF SG L))
    x y g
  ≡ @gray_transf_graph_arrow
      B C
      (@strict_functor B C SF)
      (@strict_functor B C SG)
      L x y g;

assert [B C : Cat]
  (SF SG : τ (@StrictFunctor B C))
  (L : τ (@LaxTransfor
    B C
    (@strict_functor B C SF)
    (@strict_functor B C SG))) ⊢
  @eq_refl
    (Functor B (@LaxArrow_cat C))
    (@strict_functor
      B (@LaxArrow_cat C)
      (@strict_gray_transf_graph B C SF SG L))
  : τ (@=
      (Functor B (@LaxArrow_cat C))
      (@strict_functor
        B (@LaxArrow_cat C)
        (@strict_gray_transf_graph B C SF SG L))
      (@gray_transf_graph_func
        B C
        (@strict_functor B C SF)
        (@strict_functor B C SG)
        L));

assert [B C : Cat]
  (SF SG : τ (@StrictFunctor B C))
  (L : τ (@LaxTransfor
    B C
    (@strict_functor B C SF)
    (@strict_functor B C SG)))
  (x : τ (Obj B)) ⊢
  @fapp0
    B (@LaxArrow_cat C)
    (@strict_functor
      B (@LaxArrow_cat C)
      (@strict_gray_transf_graph B C SF SG L))
    x
  ≡ @gray_transf_graph_obj
      B C
      (@strict_functor B C SF)
      (@strict_functor B C SG)
      L x;

assertnot [B C : Cat]
  (SF SG : τ (@StrictFunctor B C))
  (L : τ (@LaxTransfor
    B C
    (@strict_functor B C SF)
    (@strict_functor B C SG)))
  [x y : τ (Obj B)]
  (g : τ (Hom B x y)) ⊢
  @fapp1_fapp0
    B (@LaxArrow_cat C)
    (@strict_functor
      B (@LaxArrow_cat C)
      (@strict_gray_transf_graph B C SF SG L))
    x y g
  ≡ @gray_transf_graph_arrow
      B C
      (@strict_functor B C SF)
      (@strict_functor B C SG)
      L x y g;

// The classified graph reconstructs strictness canonically; its admission
// certificate is not projected from the opaque object.
assert [B C : Cat]
  (SF SG : τ (@StrictFunctor B C))
  (L : τ (@LaxTransfor
    B C
    (@strict_functor B C SF)
    (@strict_functor B C SG))) ⊢
  @strict_functor_is_strict
    B (@LaxArrow_cat C)
    (@strict_gray_transf_graph B C SF SG L)
  : τ (@IsStrictFunctor
      B (@LaxArrow_cat C)
      (@strict_functor
        B (@LaxArrow_cat C)
        (@strict_gray_transf_graph B C SF SG L)));
