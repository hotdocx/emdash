/*
  Emdash v3.2: constructor-visible cubical-square identity and pasting.

  Pasting post-whiskers the first filler by the second lower side,
  pre-whiskers the second filler by the first upper side, and composes those
  two cells in the ordinary hom category. Existing proof-time associativity
  presents the result at the composite sides; no cubical-specific coherence
  equation, filler, or unifier is added.

  These readable terms record the provisional hand presentation used before
  CubicalArrow_cat became a transparent alias of the Sigma-derived lax-arrow
  category. Category identity and composition now remain at their generic
  nested-Sigma owners; no competing constructor rules are installed here.
  The current global strict identity/associativity endpoint cuts are used only
  to type the readable cell terms below.
*/

require open emdash.emdash3_2_cubical_arrow;

// Post-whisker the square filler alpha by the second lower side d.
symbol cubical_square_postwhisker
  [C : Cat]
  [x1 y1 z1 x2 y2 z2 : τ (Obj C)]
  (u : τ (Hom C x1 x2))
  (v : τ (Hom C y1 y2))
  (a : τ (Hom C x1 y1))
  (b : τ (Hom C x2 y2))
  (d : τ (Hom C y2 z2))
  (alpha : τ (Obj
    (@homdc_square_fibre C x1 y1 x2 y2 u v a b)))
  : τ (Hom
      (Hom_cat C x1 z2)
      (@comp_fapp0 C x1 y2 z2 d
        (@comp_fapp0 C x1 x2 y2 b u))
      (@comp_fapp0 C x1 y2 z2 d
        (@comp_fapp0 C x1 y1 y2 v a)))
≔ @hom_postcomp_fapp1_fapp0
    C C (@id_func C)
    x1 y2 z2 d
    (@comp_fapp0 C x1 x2 y2 b u)
    (@comp_fapp0 C x1 y1 y2 v a)
    alpha;

// Pre-whisker the second square filler beta by the first upper side a.
symbol cubical_square_prewhisker
  [C : Cat]
  [x1 y1 z1 y2 z2 : τ (Obj C)]
  (v : τ (Hom C y1 y2))
  (w : τ (Hom C z1 z2))
  (a : τ (Hom C x1 y1))
  (c : τ (Hom C y1 z1))
  (d : τ (Hom C y2 z2))
  (beta : τ (Obj
    (@homdc_square_fibre C y1 z1 y2 z2 v w c d)))
  : τ (Hom
      (Hom_cat C x1 z2)
      (@comp_fapp0 C x1 y1 z2
        (@comp_fapp0 C y1 y2 z2 d v) a)
      (@comp_fapp0 C x1 y1 z2
        (@comp_fapp0 C y1 z1 z2 w c) a))
≔ @hom_precomp_along_fapp1_fapp0
    C C (@id_func C)
    z2 x1 y1 a
    (@comp_fapp0 C y1 y2 z2 d v)
    (@comp_fapp0 C y1 z1 z2 w c)
    beta;

// Paste the two whiskered cells. Existing proof-time associativity aligns
// the middle and presents the outer endpoints in composite-side form.
symbol cubical_square_paste_cell
  [C : Cat]
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
    (@homdc_square_fibre C y1 z1 y2 z2 v w c d)))
  : τ (Hom
      (Hom_cat C x1 z2)
      (@comp_fapp0 C x1 x2 z2
        (@comp_fapp0 C x2 y2 z2 d b) u)
      (@comp_fapp0 C x1 z1 z2 w
        (@comp_fapp0 C x1 y1 z1 c a)))
≔ @comp_fapp0
    (Hom_cat C x1 z2)
    (@comp_fapp0 C x1 y2 z2 d
      (@comp_fapp0 C x1 x2 y2 b u))
    (@comp_fapp0 C x1 y1 z2
      (@comp_fapp0 C y1 y2 z2 d v) a)
    (@comp_fapp0 C x1 y1 z2
      (@comp_fapp0 C y1 z1 z2 w c) a)
    (@cubical_square_prewhisker
      C x1 y1 z1 y2 z2 v w a c d beta)
    (@cubical_square_postwhisker
      C x1 y1 z1 x2 y2 z2 u v a b d alpha);

symbol cubical_square_id
  [C : Cat]
  [x y : τ (Obj C)]
  (u : τ (Hom C x y))
  : τ (Hom
      (@CubicalArrow_cat C)
      (@cubical_edge C x y u)
      (@cubical_edge C x y u))
≔ @cubical_square
    C x x y y
    u u
    (@id C x)
    (@id C y)
    (@id (Hom_cat C x y) u);

symbol cubical_square_comp
  [C : Cat]
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
    (@homdc_square_fibre C y1 z1 y2 z2 v w c d)))
  : τ (Hom
      (@CubicalArrow_cat C)
      (@cubical_edge C x1 x2 u)
      (@cubical_edge C z1 z2 w))
≔ @cubical_square
    C x1 z1 x2 z2
    u w
    (@comp_fapp0 C x1 y1 z1 c a)
    (@comp_fapp0 C x2 y2 z2 d b)
    (@cubical_square_paste_cell
      C x1 y1 z1 x2 y2 z2
      u v w a b c d alpha beta);
