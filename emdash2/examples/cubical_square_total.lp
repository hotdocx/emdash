/*
  Reviewer example: the fixed-boundary square total and its six-face next
  action. The top and bottom coordinates vary; the fixed vertical boundary
  produces two intentionally degenerate side faces.
*/

require open emdash.emdash3_2_cubical_square_total;
// The two varying line observations compute from whole Sigma projections.
assert [K1 K2 : Cat]
  (E : τ (Functor (Op_cat K1) (Catd_cat K2)))
  [x1 y1 : τ (Obj K1)]
  [x2 y2 : τ (Obj K2)]
  (u : τ (Obj (Fibre_cat
    (@fapp0 (Op_cat K1) (Catd_cat K2) E x1) x2)))
  (v : τ (Obj (Fibre_cat
    (@fapp0 (Op_cat K1) (Catd_cat K2) E y1) y2)))
  (a : τ (Hom K1 x1 y1))
  (b : τ (Hom K2 x2 y2))
  (alpha : τ (Obj
    (@homdc_fibre K1 K2 E x1 y1 x2 y2 u v a b))) ⊢
  @fapp0
    (@homdc_square_cat K1 K2 E x1 y1 x2 y2 u v)
    (Hom_cat K1 x1 y1)
    (@homdc_square_top_func K1 K2 E x1 y1 x2 y2 u v)
    (@homdc_square_obj K1 K2 E x1 y1 x2 y2 u v a b alpha)
  ≡ a;

assert [K1 K2 : Cat]
  (E : τ (Functor (Op_cat K1) (Catd_cat K2)))
  [x1 y1 : τ (Obj K1)]
  [x2 y2 : τ (Obj K2)]
  (u : τ (Obj (Fibre_cat
    (@fapp0 (Op_cat K1) (Catd_cat K2) E x1) x2)))
  (v : τ (Obj (Fibre_cat
    (@fapp0 (Op_cat K1) (Catd_cat K2) E y1) y2)))
  (a : τ (Hom K1 x1 y1))
  (b : τ (Hom K2 x2 y2))
  (alpha : τ (Obj
    (@homdc_fibre K1 K2 E x1 y1 x2 y2 u v a b))) ⊢
  @piapp0
    (@homdc_square_cat K1 K2 E x1 y1 x2 y2 u v)
    (@homdc_square_bottom_catd
      K1 K2 E x1 y1 x2 y2 u v)
    (@homdc_square_bottom_sec K1 K2 E x1 y1 x2 y2 u v)
    (@homdc_square_obj K1 K2 E x1 y1 x2 y2 u v a b alpha)
  ≡ b;

assert [K1 K2 : Cat]
  (E : τ (Functor (Op_cat K1) (Catd_cat K2)))
  [x1 y1 : τ (Obj K1)]
  [x2 y2 : τ (Obj K2)]
  (u : τ (Obj (Fibre_cat
    (@fapp0 (Op_cat K1) (Catd_cat K2) E x1) x2)))
  (v : τ (Obj (Fibre_cat
    (@fapp0 (Op_cat K1) (Catd_cat K2) E y1) y2)))
  (a : τ (Hom K1 x1 y1))
  (b : τ (Hom K2 x2 y2))
  (alpha : τ (Obj
    (@homdc_fibre K1 K2 E x1 y1 x2 y2 u v a b))) ⊢
  @fapp0
    (@homdc_square_cat K1 K2 E x1 y1 x2 y2 u v)
    (Fibre_cat (@fapp0 (Op_cat K1) (Catd_cat K2) E x1) x2)
    (@homdc_square_left_func K1 K2 E x1 y1 x2 y2 u v)
    (@homdc_square_obj K1 K2 E x1 y1 x2 y2 u v a b alpha)
  ≡ u;

assert [K1 K2 : Cat]
  (E : τ (Functor (Op_cat K1) (Catd_cat K2)))
  [x1 y1 : τ (Obj K1)]
  [x2 y2 : τ (Obj K2)]
  (u : τ (Obj (Fibre_cat
    (@fapp0 (Op_cat K1) (Catd_cat K2) E x1) x2)))
  (v : τ (Obj (Fibre_cat
    (@fapp0 (Op_cat K1) (Catd_cat K2) E y1) y2)))
  (a : τ (Hom K1 x1 y1))
  (b : τ (Hom K2 x2 y2))
  (alpha : τ (Obj
    (@homdc_fibre K1 K2 E x1 y1 x2 y2 u v a b))) ⊢
  @fapp0
    (@homdc_square_cat K1 K2 E x1 y1 x2 y2 u v)
    (Fibre_cat (@fapp0 (Op_cat K1) (Catd_cat K2) E y1) y2)
    (@homdc_square_right_func K1 K2 E x1 y1 x2 y2 u v)
    (@homdc_square_obj K1 K2 E x1 y1 x2 y2 u v a b alpha)
  ≡ v;

// The next-hom owner takes a volume theta between two constructor-visible
// square objects. Its ordinary source and target are the first two faces; the
// four operations below are the remaining side-face observations.
type @homdc_cube_top_face;
type @homdc_cube_bottom_face;
type @homdc_cube_left_face;
type @homdc_cube_right_face;

// The two fixed-boundary side faces compute to identities rather than being
// postulated opaque fillers.
assert [K1 K2 : Cat]
  (E : τ (Functor (Op_cat K1) (Catd_cat K2)))
  [x1 y1 : τ (Obj K1)]
  [x2 y2 : τ (Obj K2)]
  (u : τ (Obj (Fibre_cat
    (@fapp0 (Op_cat K1) (Catd_cat K2) E x1) x2)))
  (v : τ (Obj (Fibre_cat
    (@fapp0 (Op_cat K1) (Catd_cat K2) E y1) y2)))
  [a a' : τ (Hom K1 x1 y1)]
  [b b' : τ (Hom K2 x2 y2)]
  [alpha : τ (Obj
    (@homdc_fibre K1 K2 E x1 y1 x2 y2 u v a b))]
  [beta : τ (Obj
    (@homdc_fibre K1 K2 E x1 y1 x2 y2 u v a' b'))]
  (theta : τ (Hom
    (@homdc_square_cat K1 K2 E x1 y1 x2 y2 u v)
    (@homdc_square_obj K1 K2 E x1 y1 x2 y2 u v a b alpha)
    (@homdc_square_obj K1 K2 E x1 y1 x2 y2 u v a' b' beta))) ⊢
  @homdc_cube_left_face
    K1 K2 E x1 y1 x2 y2 u v a a' b b' alpha beta theta
  ≡ @id
      (Fibre_cat (@fapp0 (Op_cat K1) (Catd_cat K2) E x1) x2)
      u;

assert [K1 K2 : Cat]
  (E : τ (Functor (Op_cat K1) (Catd_cat K2)))
  [x1 y1 : τ (Obj K1)]
  [x2 y2 : τ (Obj K2)]
  (u : τ (Obj (Fibre_cat
    (@fapp0 (Op_cat K1) (Catd_cat K2) E x1) x2)))
  (v : τ (Obj (Fibre_cat
    (@fapp0 (Op_cat K1) (Catd_cat K2) E y1) y2)))
  [a a' : τ (Hom K1 x1 y1)]
  [b b' : τ (Hom K2 x2 y2)]
  [alpha : τ (Obj
    (@homdc_fibre K1 K2 E x1 y1 x2 y2 u v a b))]
  [beta : τ (Obj
    (@homdc_fibre K1 K2 E x1 y1 x2 y2 u v a' b'))]
  (theta : τ (Hom
    (@homdc_square_cat K1 K2 E x1 y1 x2 y2 u v)
    (@homdc_square_obj K1 K2 E x1 y1 x2 y2 u v a b alpha)
    (@homdc_square_obj K1 K2 E x1 y1 x2 y2 u v a' b' beta))) ⊢
  @homdc_cube_right_face
    K1 K2 E x1 y1 x2 y2 u v a a' b b' alpha beta theta
  ≡ @id
      (Fibre_cat (@fapp0 (Op_cat K1) (Catd_cat K2) E y1) y2)
      v;
