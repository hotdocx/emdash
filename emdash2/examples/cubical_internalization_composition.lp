/*
  Reviewer example: generic identity and composition in the Sigma-derived
  lax-arrow category retain the expected cubical side boundaries.

  The full nested constructor terms deliberately remain at the canonical
  Sigma/internal-action owners; they are not collapsed to the provisional
  hand-presented square-pasting formula.
*/

require open emdash.emdash3_2_cubical_internalization;

// Generic identity has the expected source and target boundary identities.
assert [C : Cat]
  [x y : τ (Obj C)]
  (u : τ (Hom C x y)) ⊢
  @fapp1_fapp0
    (@LaxArrow_cat C)
    C
    (@homdc_total_source_func C C (@hom_int C C (@id_func C)))
    (@lax_edge C x y u)
    (@lax_edge C x y u)
    (@id (@LaxArrow_cat C) (@lax_edge C x y u))
  ≡ @id C x;

assert [C : Cat]
  [x y : τ (Obj C)]
  (u : τ (Hom C x y)) ⊢
  @fapp1_fapp0
    (@LaxArrow_cat C)
    C
    (@homdc_total_target_func C C (@hom_int C C (@id_func C)))
    (@lax_edge C x y u)
    (@lax_edge C x y u)
    (@id (@LaxArrow_cat C) (@lax_edge C x y u))
  ≡ @id C y;

// Generic composition has the expected composite source and target sides.
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
    (@LaxArrow_cat C)
    C
    (@homdc_total_source_func C C (@hom_int C C (@id_func C)))
    (@lax_edge C x1 x2 u)
    (@lax_edge C z1 z2 w)
    (@comp_fapp0
      (@LaxArrow_cat C)
      (@lax_edge C x1 x2 u)
      (@lax_edge C y1 y2 v)
      (@lax_edge C z1 z2 w)
      (@lax_square C y1 z1 y2 z2 v w c d beta)
      (@lax_square C x1 y1 x2 y2 u v a b alpha))
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
    (@LaxArrow_cat C)
    C
    (@homdc_total_target_func C C (@hom_int C C (@id_func C)))
    (@lax_edge C x1 x2 u)
    (@lax_edge C z1 z2 w)
    (@comp_fapp0
      (@LaxArrow_cat C)
      (@lax_edge C x1 x2 u)
      (@lax_edge C y1 y2 v)
      (@lax_edge C z1 z2 w)
      (@lax_square C y1 z1 y2 z2 v w c d beta)
      (@lax_square C x1 y1 x2 y2 u v a b alpha))
  ≡ @comp_fapp0 C x2 y2 z2 d b;

// The Hom actions of both endpoint functors remain available, so a next
// cubical level does not require capped face records.
type @homdc_total_source_func;
type @homdc_total_target_func;
