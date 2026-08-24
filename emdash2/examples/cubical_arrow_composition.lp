/*
  Reviewer example: cubical-arrow identity, pasted composition, and retained
  whole source/target action.
*/

require open emdash.emdash3_2_cubical_arrow_composition;

// The readable identity square remains a well-typed arrow. Category identity
// itself stays at the canonical nested-Sigma owner.
assert [C : Cat]
  (x y : τ (Obj C))
  (u : τ (Hom C x y)) ⊢
  @cubical_square_id C x y u
  : τ (Hom
      (@CubicalArrow_cat C)
      (@cubical_edge C x y u)
      (@cubical_edge C x y u));

// The readable whisker-and-paste composite also remains a well-typed arrow;
// it is not selected as a second runtime normal form.
assert [C : Cat]
  [x1 y1 z1 x2 y2 z2 : τ (Obj C)]
  (u : τ (Hom C x1 x2))
  (v : τ (Hom C y1 y2))
  (w : τ (Hom C z1 z2))
  (a : τ (Hom C x1 y1))
  (b : τ (Hom C x2 y2))
  (c : τ (Hom C y1 z1))
  (d : τ (Hom C y2 z2))
  (alpha : τ (Obj
    (@homdc_square_fibre C x1 y1 x2 y2 u v a b)))
  (beta : τ (Obj
    (@homdc_square_fibre C y1 z1 y2 z2 v w c d))) ⊢
  @cubical_square_comp
    C x1 y1 z1 x2 y2 z2
    u v w a b c d alpha beta
  : τ (Hom
    (@CubicalArrow_cat C)
    (@cubical_edge C x1 x2 u)
    (@cubical_edge C z1 z2 w));

// The pasted filler is a genuine cell at the composite sides.
assert [C : Cat]
  [x1 y1 z1 x2 y2 z2 : τ (Obj C)]
  (u : τ (Hom C x1 x2))
  (v : τ (Hom C y1 y2))
  (w : τ (Hom C z1 z2))
  (a : τ (Hom C x1 y1))
  (b : τ (Hom C x2 y2))
  (c : τ (Hom C y1 z1))
  (d : τ (Hom C y2 z2))
  (alpha : τ (Obj
    (@homdc_square_fibre C x1 y1 x2 y2 u v a b)))
  (beta : τ (Obj
    (@homdc_square_fibre C y1 z1 y2 z2 v w c d))) ⊢
  @cubical_square_paste_cell
    C x1 y1 z1 x2 y2 z2
    u v w a b c d alpha beta
  : τ (Hom
      (Hom_cat C x1 z2)
      (@comp_fapp0 C x1 x2 z2
        (@comp_fapp0 C x2 y2 z2 d b) u)
      (@comp_fapp0 C x1 z1 z2 w
        (@comp_fapp0 C x1 y1 z1 c a)));

// Whole hom actions of the face functors retain the square and project it.
assert [C : Cat]
  [x1 y1 x2 y2 : τ (Obj C)]
  (u : τ (Hom C x1 x2))
  (v : τ (Hom C y1 y2))
  (a : τ (Hom C x1 y1))
  (b : τ (Hom C x2 y2))
  (alpha : τ (Obj
    (@homdc_square_fibre C x1 y1 x2 y2 u v a b))) ⊢
  @fapp0
    (Hom_cat
      (@CubicalArrow_cat C)
      (@cubical_edge C x1 x2 u)
      (@cubical_edge C y1 y2 v))
    (Hom_cat C x1 y1)
    (@fapp1_func
      (@CubicalArrow_cat C) C
      (@cubical_src_func C)
      (@cubical_edge C x1 x2 u)
      (@cubical_edge C y1 y2 v))
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
  @fapp0
    (Hom_cat
      (@CubicalArrow_cat C)
      (@cubical_edge C x1 x2 u)
      (@cubical_edge C y1 y2 v))
    (Hom_cat C x2 y2)
    (@fapp1_func
      (@CubicalArrow_cat C) C
      (@cubical_tgt_func C)
      (@cubical_edge C x1 x2 u)
      (@cubical_edge C y1 y2 v))
    (@cubical_square C x1 y1 x2 y2 u v a b alpha)
  ≡ b;

// Generic functoriality agrees with the visible composite side projections.
assert [C : Cat]
  [x1 y1 z1 x2 y2 z2 : τ (Obj C)]
  (u : τ (Hom C x1 x2))
  (v : τ (Hom C y1 y2))
  (w : τ (Hom C z1 z2))
  (a : τ (Hom C x1 y1))
  (b : τ (Hom C x2 y2))
  (c : τ (Hom C y1 z1))
  (d : τ (Hom C y2 z2))
  (alpha : τ (Obj
    (@homdc_square_fibre C x1 y1 x2 y2 u v a b)))
  (beta : τ (Obj
    (@homdc_square_fibre C y1 z1 y2 z2 v w c d))) ⊢
  @fapp1_fapp0
    (@CubicalArrow_cat C) C
    (@cubical_src_func C)
    (@cubical_edge C x1 x2 u)
    (@cubical_edge C z1 z2 w)
    (@cubical_square_comp
      C x1 y1 z1 x2 y2 z2
      u v w a b c d alpha beta)
  ≡ @comp_fapp0 C x1 y1 z1 c a;

assert [C : Cat]
  [x1 y1 z1 x2 y2 z2 : τ (Obj C)]
  (u : τ (Hom C x1 x2))
  (v : τ (Hom C y1 y2))
  (w : τ (Hom C z1 z2))
  (a : τ (Hom C x1 y1))
  (b : τ (Hom C x2 y2))
  (c : τ (Hom C y1 z1))
  (d : τ (Hom C y2 z2))
  (alpha : τ (Obj
    (@homdc_square_fibre C x1 y1 x2 y2 u v a b)))
  (beta : τ (Obj
    (@homdc_square_fibre C y1 z1 y2 z2 v w c d))) ⊢
  @fapp1_fapp0
    (@CubicalArrow_cat C) C
    (@cubical_tgt_func C)
    (@cubical_edge C x1 x2 u)
    (@cubical_edge C z1 z2 w)
    (@cubical_square_comp
      C x1 y1 z1 x2 y2 z2
      u v w a b c d alpha beta)
  ≡ @comp_fapp0 C x2 y2 z2 d b;
