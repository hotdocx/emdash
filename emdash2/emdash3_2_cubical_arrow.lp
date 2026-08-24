/*
  Emdash v3.2: readable aliases for the derived directed lax-arrow category.

  Objects are arrows u:x->y. The Hom between two visible arrow objects is
  the already-checked two-sided square total, so its objects are directed
  lax squares alpha:b o u => v o a with both side arrows variable.

  The category, objects, square objects, and whole source/target functors now
  delegate to the variance-correct homdc_int/Sigma construction.  This module
  owns no independent category, Hom, endpoint action, square, rule, or
  unifier.  The historical names remain as a migration/readability facade.
*/

require open emdash.emdash3_2_cubical_internalization;

symbol CubicalArrow_cat
  (C : Cat)
  : Cat
≔ @LaxArrow_cat C;

symbol cubical_edge
  [C : Cat]
  (x y : τ (Obj C))
  (u : τ (Hom C x y))
  : τ (Obj (@CubicalArrow_cat C))
≔ @lax_edge C x y u;

symbol cubical_square
  [C : Cat]
  [x1 y1 x2 y2 : τ (Obj C)]
  (u : τ (Hom C x1 x2))
  (v : τ (Hom C y1 y2))
  (a : τ (Hom C x1 y1))
  (b : τ (Hom C x2 y2))
  (alpha : τ (Obj
    (@homdc_square_fibre C x1 y1 x2 y2 u v a b)))
  : τ (Hom
      (@CubicalArrow_cat C)
      (@cubical_edge C x1 x2 u)
      (@cubical_edge C y1 y2 v))
≔ @lax_square C x1 y1 x2 y2 u v a b alpha;

symbol cubical_src_func
  (C : Cat)
  : τ (Functor (@CubicalArrow_cat C) C)
≔ @homdc_total_source_func
    C C
    (@hom_int C C (@id_func C));

symbol cubical_tgt_func
  (C : Cat)
  : τ (Functor (@CubicalArrow_cat C) C)
≔ @homdc_total_target_func
    C C
    (@hom_int C C (@id_func C));
