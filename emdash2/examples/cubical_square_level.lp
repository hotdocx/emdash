/*
  Reviewer example: variable-boundary squares and six-face cube action.
*/

require open emdash.emdash3_2_cubical_square_level;

// The four faces of one visible square recover its four independently
// supplied boundary edges.
assert [C : Cat]
  [x1 y1 x2 y2 : τ (Obj C)]
  (u : τ (Hom C x1 x2))
  (v : τ (Hom C y1 y2))
  (a : τ (Hom C x1 y1))
  (b : τ (Hom C x2 y2))
  (alpha : τ (Obj
    (@homdc_square_fibre C x1 y1 x2 y2 u v a b))) ⊢
  @fapp0
    (@CubicalSquare_cat C) (@CubicalArrow_cat C)
    (@cubical_square_outer_src_func C)
    (@cubical_square_object C x1 y1 x2 y2 u v a b alpha)
  ≡ @cubical_edge C x1 x2 u;

assert [C : Cat]
  [x1 y1 x2 y2 : τ (Obj C)]
  (u : τ (Hom C x1 x2))
  (v : τ (Hom C y1 y2))
  (a : τ (Hom C x1 y1))
  (b : τ (Hom C x2 y2))
  (alpha : τ (Obj
    (@homdc_square_fibre C x1 y1 x2 y2 u v a b))) ⊢
  @fapp0
    (@CubicalSquare_cat C) (@CubicalArrow_cat C)
    (@cubical_square_outer_tgt_func C)
    (@cubical_square_object C x1 y1 x2 y2 u v a b alpha)
  ≡ @cubical_edge C y1 y2 v;

assert [C : Cat]
  [x1 y1 x2 y2 : τ (Obj C)]
  (u : τ (Hom C x1 x2))
  (v : τ (Hom C y1 y2))
  (a : τ (Hom C x1 y1))
  (b : τ (Hom C x2 y2))
  (alpha : τ (Obj
    (@homdc_square_fibre C x1 y1 x2 y2 u v a b))) ⊢
  @fapp0
    (@CubicalSquare_cat C) (@CubicalArrow_cat C)
    (@cubical_square_inner_src_func C)
    (@cubical_square_object C x1 y1 x2 y2 u v a b alpha)
  ≡ @cubical_edge C x1 y1 a;

assert [C : Cat]
  [x1 y1 x2 y2 : τ (Obj C)]
  (u : τ (Hom C x1 x2))
  (v : τ (Hom C y1 y2))
  (a : τ (Hom C x1 y1))
  (b : τ (Hom C x2 y2))
  (alpha : τ (Obj
    (@homdc_square_fibre C x1 y1 x2 y2 u v a b))) ⊢
  @fapp0
    (@CubicalSquare_cat C) (@CubicalArrow_cat C)
    (@cubical_square_inner_tgt_func C)
    (@cubical_square_object C x1 y1 x2 y2 u v a b alpha)
  ≡ @cubical_edge C x2 y2 b;

// For theta:S->T, S and T are two endpoint square faces; these four whole
// actions are the remaining side-square faces.
type @cubical_cube_outer_src;
type @cubical_cube_outer_tgt;
type @cubical_cube_inner_src;
type @cubical_cube_inner_tgt;

// None of the four face functors is definitionally collapsed to another.
assertnot [C : Cat] ⊢
  @cubical_square_outer_src_func C
  ≡ @cubical_square_outer_tgt_func C;

assertnot [C : Cat] ⊢
  @cubical_square_inner_src_func C
  ≡ @cubical_square_inner_tgt_func C;

assertnot [C : Cat] ⊢
  @cubical_square_outer_src_func C
  ≡ @cubical_square_inner_src_func C;

// All face functors retain pseudo properties for another CubicalArrow lift.
assert [C : Cat] ⊢
  @cubical_square_outer_src_is_pseudo C
  : τ (@IsPseudoFunctor
      (@CubicalSquare_cat C) (@CubicalArrow_cat C)
      (@cubical_square_outer_src_func C));

assert [C : Cat] ⊢
  @cubical_square_inner_tgt_is_pseudo C
  : τ (@IsPseudoFunctor
      (@CubicalSquare_cat C) (@CubicalArrow_cat C)
      (@cubical_square_inner_tgt_func C));
