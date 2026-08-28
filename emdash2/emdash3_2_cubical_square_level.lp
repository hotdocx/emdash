/*
  Emdash v3.2: the first iterated intrinsic cubical-arrow level.

  CubicalSquare_cat(C) is CubicalArrow(CubicalArrow(C)). Its objects are
  variable-boundary directed squares. Four whole edge-face functors arise
  recursively: outer source/target and CubicalArrow lifts of the inner
  source/target. An arrow between two square objects therefore has two
  endpoint square faces plus four side-square actions.

  Every face retains the pseudo-functor property for subsequent iteration.
  This module adds no rule, face equation, Gray comparison, or code syntax.
*/

require open emdash.emdash3_2_cubical_arrow_functor;

symbol CubicalSquare_cat
  (C : Cat)
  : Cat
≔ @CubicalArrow_cat (@CubicalArrow_cat C);

// Four edge-face functors of a square object.
symbol cubical_square_outer_src_func
  (C : Cat)
  : τ (Functor (@CubicalSquare_cat C) (@CubicalArrow_cat C))
≔ @cubical_src_func (@CubicalArrow_cat C);

symbol cubical_square_outer_tgt_func
  (C : Cat)
  : τ (Functor (@CubicalSquare_cat C) (@CubicalArrow_cat C))
≔ @cubical_tgt_func (@CubicalArrow_cat C);

symbol cubical_square_inner_src_func
  (C : Cat)
  : τ (Functor (@CubicalSquare_cat C) (@CubicalArrow_cat C))
≔ @CubicalArrow_func
    (@CubicalArrow_cat C) C
    (@cubical_src_func C)
    (@cubical_src_is_pseudo C);

symbol cubical_square_inner_tgt_func
  (C : Cat)
  : τ (Functor (@CubicalSquare_cat C) (@CubicalArrow_cat C))
≔ @CubicalArrow_func
    (@CubicalArrow_cat C) C
    (@cubical_tgt_func C)
    (@cubical_tgt_is_pseudo C);

// A constructor-visible square is an arrow object in CubicalArrow(C).
symbol cubical_square_object
  [C : Cat]
  [x1 y1 x2 y2 : τ (Obj C)]
  (u : τ (Hom C x1 x2))
  (v : τ (Hom C y1 y2))
  (a : τ (Hom C x1 y1))
  (b : τ (Hom C x2 y2))
  (alpha : τ (Obj
    (@homdc_square_fibre C x1 y1 x2 y2 u v a b)))
  : τ (Obj (@CubicalSquare_cat C))
≔ @cubical_edge
    (@CubicalArrow_cat C)
    (@cubical_edge C x1 x2 u)
    (@cubical_edge C y1 y2 v)
    (@cubical_square C x1 y1 x2 y2 u v a b alpha);

// Four side-square faces of a cube theta. Its other two faces are S and T.
symbol cubical_cube_outer_src
  [C : Cat]
  [S T : τ (Obj (@CubicalSquare_cat C))]
  (theta : τ (Hom (@CubicalSquare_cat C) S T))
  : τ (Hom
      (@CubicalArrow_cat C)
      (@fapp0
        (@CubicalSquare_cat C) (@CubicalArrow_cat C)
        (@cubical_square_outer_src_func C) S)
      (@fapp0
        (@CubicalSquare_cat C) (@CubicalArrow_cat C)
        (@cubical_square_outer_src_func C) T))
≔ @fapp1_fapp0
    (@CubicalSquare_cat C) (@CubicalArrow_cat C)
    (@cubical_square_outer_src_func C) S T theta;

symbol cubical_cube_outer_tgt
  [C : Cat]
  [S T : τ (Obj (@CubicalSquare_cat C))]
  (theta : τ (Hom (@CubicalSquare_cat C) S T))
  : τ (Hom
      (@CubicalArrow_cat C)
      (@fapp0
        (@CubicalSquare_cat C) (@CubicalArrow_cat C)
        (@cubical_square_outer_tgt_func C) S)
      (@fapp0
        (@CubicalSquare_cat C) (@CubicalArrow_cat C)
        (@cubical_square_outer_tgt_func C) T))
≔ @fapp1_fapp0
    (@CubicalSquare_cat C) (@CubicalArrow_cat C)
    (@cubical_square_outer_tgt_func C) S T theta;

symbol cubical_cube_inner_src
  [C : Cat]
  [S T : τ (Obj (@CubicalSquare_cat C))]
  (theta : τ (Hom (@CubicalSquare_cat C) S T))
  : τ (Hom
      (@CubicalArrow_cat C)
      (@fapp0
        (@CubicalSquare_cat C) (@CubicalArrow_cat C)
        (@cubical_square_inner_src_func C) S)
      (@fapp0
        (@CubicalSquare_cat C) (@CubicalArrow_cat C)
        (@cubical_square_inner_src_func C) T))
≔ @fapp1_fapp0
    (@CubicalSquare_cat C) (@CubicalArrow_cat C)
    (@cubical_square_inner_src_func C) S T theta;

symbol cubical_cube_inner_tgt
  [C : Cat]
  [S T : τ (Obj (@CubicalSquare_cat C))]
  (theta : τ (Hom (@CubicalSquare_cat C) S T))
  : τ (Hom
      (@CubicalArrow_cat C)
      (@fapp0
        (@CubicalSquare_cat C) (@CubicalArrow_cat C)
        (@cubical_square_inner_tgt_func C) S)
      (@fapp0
        (@CubicalSquare_cat C) (@CubicalArrow_cat C)
        (@cubical_square_inner_tgt_func C) T))
≔ @fapp1_fapp0
    (@CubicalSquare_cat C) (@CubicalArrow_cat C)
    (@cubical_square_inner_tgt_func C) S T theta;

// Pseudo properties for all four face functors survive to the next level.
symbol cubical_square_outer_src_is_pseudo
  (C : Cat)
  : τ (@IsPseudoFunctor
      (@CubicalSquare_cat C) (@CubicalArrow_cat C)
      (@cubical_square_outer_src_func C))
≔ @cubical_src_is_pseudo (@CubicalArrow_cat C);

symbol cubical_square_outer_tgt_is_pseudo
  (C : Cat)
  : τ (@IsPseudoFunctor
      (@CubicalSquare_cat C) (@CubicalArrow_cat C)
      (@cubical_square_outer_tgt_func C))
≔ @cubical_tgt_is_pseudo (@CubicalArrow_cat C);

symbol cubical_square_inner_src_is_pseudo
  (C : Cat)
  : τ (@IsPseudoFunctor
      (@CubicalSquare_cat C) (@CubicalArrow_cat C)
      (@cubical_square_inner_src_func C))
≔ @cubical_arrow_is_pseudo
    (@CubicalArrow_cat C) C
    (@cubical_src_func C)
    (@cubical_src_is_pseudo C);

symbol cubical_square_inner_tgt_is_pseudo
  (C : Cat)
  : τ (@IsPseudoFunctor
      (@CubicalSquare_cat C) (@CubicalArrow_cat C)
      (@cubical_square_inner_tgt_func C))
≔ @cubical_arrow_is_pseudo
    (@CubicalArrow_cat C) C
    (@cubical_tgt_func C)
    (@cubical_tgt_is_pseudo C);
