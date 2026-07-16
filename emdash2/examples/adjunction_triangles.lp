/*
  Reviewer milestone: indexed adjunction cut-elimination and mates.

  An adjunction witness is indexed by its already-named left/right functors.
  Unit/counit observations remain stable runtime heads, so both triangles
  compute without equations identifying them with unrelated named operations.
*/

require open emdash.emdash3_2;

// Left triangle: counit[f] ∘ F(unit[g]) ↪ f ∘ F(g).
assert [R L : Cat]
  [F : τ (Functor R L)]
  [G : τ (Functor L R)]
  (J : τ (@Adjunction R L F G))
  (X X' : τ (Obj R))
  (Y : τ (Obj L))
  (g : τ (Hom R X X'))
  (f : τ (Hom L (@fapp0 R L F X') Y)) ⊢
  comp_fapp0
    (@tapp1_fapp0
      L L
      (@comp_cat_fapp0 L R L F G)
      (@id_func L)
      (@fapp0 R L F X')
      Y
      (@counit_adj_transf R L F G J)
      f)
    (@fapp1_fapp0
      R L F
      X
      (@fapp0 L R G (@fapp0 R L F X'))
      (@tapp1_fapp0
        R R
        (@id_func R)
        (@comp_cat_fapp0 R L R G F)
        X X'
        (@unit_adj_transf R L F G J)
        g))
  ≡ comp_fapp0 f (@fapp1_fapp0 R L F X X' g);

// Right triangle: G(counit[g]) ∘ unit[f] ↪ G(g) ∘ f.
assert [R L : Cat]
  [F : τ (Functor R L)]
  [G : τ (Functor L R)]
  (J : τ (@Adjunction R L F G))
  (X : τ (Obj R))
  (Y' Y : τ (Obj L))
  (f : τ (Hom R X (@fapp0 L R G Y')))
  (g : τ (Hom L Y' Y)) ⊢
  comp_fapp0
    (@fapp1_fapp0
      L R G
      (@fapp0 R L F (@fapp0 L R G Y'))
      Y
      (@tapp1_fapp0
        L L
        (@comp_cat_fapp0 L R L F G)
        (@id_func L)
        Y' Y
        (@counit_adj_transf R L F G J)
        g))
    (@tapp1_fapp0
      R R
      (@id_func R)
      (@comp_cat_fapp0 R L R G F)
      X
      (@fapp0 L R G Y')
      (@unit_adj_transf R L F G J)
      f)
  ≡ comp_fapp0 (@fapp1_fapp0 L R G Y' Y g) f;

// Opposite adjunction swaps the functor indices and is involutive.
assert [A B : Cat]
  [F : τ (Functor A B)]
  [G : τ (Functor B A)]
  (J : τ (@Adjunction A B F G)) ⊢
  @Op_adjunction
    (Op_cat B)
    (Op_cat A)
    (@Op_func B A G)
    (@Op_func A B F)
    (@Op_adjunction A B F G J)
  ≡ J;

// The reindexed mate comparison retains its push/pull cancellation.
assert [A B I K : Cat]
  [F : τ (Functor A B)]
  [G : τ (Functor B A)]
  (J : τ (@Adjunction A B F G))
  (M : τ (Functor I A))
  (H : τ (Functor K B))
  [P : τ (Prof I K)]
  (r : τ (ProfMap
    P
    (@Hom_prof_along
      I K B
      (@comp_cat_fapp0 I A B F M)
      H))) ⊢
  @prof_comparison_pull
    I K
    (@Hom_prof_along
      I K B
      (@comp_cat_fapp0 I A B F M)
      H)
    (@Hom_prof_along
      I K A
      M
      (@comp_cat_fapp0 K B A G H))
    (@Adjunction_hom_prof_comparison_along
      A B F G J I K M H)
    P
    (@prof_comparison_push
      I K
      (@Hom_prof_along
        I K B
        (@comp_cat_fapp0 I A B F M)
        H)
      (@Hom_prof_along
        I K A
        M
        (@comp_cat_fapp0 K B A G H))
      (@Adjunction_hom_prof_comparison_along
        A B F G J I K M H)
      P r)
  ≡ r;

// No declaration binds an arbitrary named unit to the stable observation.
assertnot [R L : Cat]
  [F : τ (Functor R L)]
  [G : τ (Functor L R)]
  (J : τ (@Adjunction R L F G))
  (eta : τ (Transf
      (@id_func R)
      (@comp_cat_fapp0 R L R G F))) ⊢
  @unit_adj_transf R L F G J
  ≡ eta;
