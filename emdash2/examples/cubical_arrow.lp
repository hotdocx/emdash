/*
  Reviewer example: intrinsic arrows, variable-boundary square Homs, and
  whole source/target observations.
*/

require open emdash.emdash3_2_cubical_arrow;
// Constructor-visible observations.
assert [C : Cat]
  (x y : τ (Obj C))
  (u : τ (Hom C x y)) ⊢
  @fapp0
    (@CubicalArrow_cat C) C
    (@cubical_src_func C)
    (@cubical_edge C x y u)
  ≡ x;

assert [C : Cat]
  (x y : τ (Obj C))
  (u : τ (Hom C x y)) ⊢
  @fapp0
    (@CubicalArrow_cat C) C
    (@cubical_tgt_func C)
    (@cubical_edge C x y u)
  ≡ y;

assert [C : Cat]
  [x1 y1 x2 y2 : τ (Obj C)]
  (u : τ (Hom C x1 x2))
  (v : τ (Hom C y1 y2))
  (a : τ (Hom C x1 y1))
  (b : τ (Hom C x2 y2))
  (alpha : τ (Obj
    (@homdc_square_fibre C x1 y1 x2 y2 u v a b))) ⊢
  @fapp1_fapp0
    (@CubicalArrow_cat C) C
    (@cubical_src_func C)
    (@cubical_edge C x1 x2 u)
    (@cubical_edge C y1 y2 v)
    (@cubical_square C x1 y1 x2 y2 u v a b alpha)
  ≡ a;

assert [C : Cat]
  [x1 y1 x2 y2 : τ (Obj C)]
  (u : τ (Hom C x1 x2))
  (v : τ (Hom C y1 y2))
  (a : τ (Hom C x1 y1))
  (b : τ (Hom C x2 y2))
  (alpha : τ (Obj
    (@homdc_square_fibre C x1 y1 x2 y2 u v a b))) ⊢
  @fapp1_fapp0
    (@CubicalArrow_cat C) C
    (@cubical_tgt_func C)
    (@cubical_edge C x1 x2 u)
    (@cubical_edge C y1 y2 v)
    (@cubical_square C x1 y1 x2 y2 u v a b alpha)
  ≡ b;
