/*
  Emdash v3.2: variance-correct cubical internal hom and derived lax-arrow
  total.

  For E : K1^op -> Catd(K2), first totalize the covariant K2 coordinate:

    EdgeFamily_E[x1] = Sigma(x2 : K2), E[x1][x2].

  Pointwise opposite then lets the existing dependent internal hom run in the
  mixed first-coordinate variance:

    D_E          = Op_catd(EdgeFamily_E),
    homdc_int(E) = homd_int(id_D_E).

  Its canonical projection order is target edge, source edge, then
  a : x1 -> y1.  The endpoint is

    Hom_{EdgeFamily_E[x1]}
      ((x2,u), EdgeFamily_E[a^op](y2,v)),

  whose ordinary Sigma-Hom decomposition exposes

    b : x2 -> y2,
    alpha : E[x1][b](u) -> E[a^op][y2](v).

  The corresponding total is constructed only from existing Sigma and
  opposite owners:

    homdc_total_cat(E) = Op(Sigma_(x1 : K1^op) D_E[x1]).

  No independent cubical category, square, two-sided Sigma, rewrite, or
  unifier is postulated in this module.
*/

require open emdash.emdash3_2_cubical_square_total;

// Inner K2-total, varying contravariantly with x1.
symbol homdc_edge_catd
  [K1 K2 : Cat]
  (E : τ (Functor (Op_cat K1) (Catd_cat K2)))
  : τ (Catd (Op_cat K1))
≔ @comp_cat_fapp0
    (Op_cat K1)
    (Catd_cat K2)
    Cat_cat
    (@Sigma_func K2)
    E;

// Pointwise opposite of the inner edge family.  This is the variance bridge,
// not a second total-category constructor.
symbol homdc_op_edge_catd
  [K1 K2 : Cat]
  (E : τ (Functor (Op_cat K1) (Catd_cat K2)))
  : τ (Catd (Op_cat K1))
≔ @Op_catd
    (Op_cat K1)
    (@homdc_edge_catd K1 K2 E);

// Whole two-sided internal hom, derived from the existing homd_int owner.
// The domain reduces from Op_catd(homdc_op_edge_catd) to homdc_edge_catd.
symbol homdc_int
  [K1 K2 : Cat]
  (E : τ (Functor (Op_cat K1) (Catd_cat K2)))
  : τ (Functord
      (@homdc_edge_catd K1 K2 E)
      (@Homd_target_catd
        (Op_cat K1)
        (@homdc_op_edge_catd K1 K2 E)))
≔ @homd_int
    (Op_cat K1)
    (@homdc_op_edge_catd K1 K2 E)
    (@homdc_op_edge_catd K1 K2 E)
    (@id_funcd
      (Op_cat K1)
      (@homdc_op_edge_catd K1 K2 E));

// Final target-edge/source-edge/a projection.  Its objects are the remaining
// pairs (b,alpha).  Writing the final homd_ projection transparently preserves
// the same normal form selected by homdc_int's existing projection ladder.
symbol homdc_at
  [K1 K2 : Cat]
  (E : τ (Functor (Op_cat K1) (Catd_cat K2)))
  (y1 : τ (Obj K1))
  (y2 : τ (Obj K2))
  (v : τ (Obj (Fibre_cat
    (@fapp0 (Op_cat K1) (Catd_cat K2) E y1)
    y2)))
  (x1 : τ (Obj K1))
  (x2 : τ (Obj K2))
  (u : τ (Obj (Fibre_cat
    (@fapp0 (Op_cat K1) (Catd_cat K2) E x1)
    x2)))
  (a : τ (Hom K1 x1 y1))
  : Cat
≔ @fapp0
    (Op_cat (Hom_cat (Op_cat K1) y1 x1))
    Cat_cat
    (@homd_
      (Op_cat K1)
      (@homdc_op_edge_catd K1 K2 E)
      (@homdc_op_edge_catd K1 K2 E)
      (@id_funcd
        (Op_cat K1)
        (@homdc_op_edge_catd K1 K2 E))
      y1
      (Struct_sigma y2 v)
      x1
      (Struct_sigma x2 u))
    a;

// Variance-correct two-sided Grothendieck total.  This is a transparent
// nested Sigma/opposite expression, not a primitive TwoSidedSigma theory.
symbol homdc_total_cat
  [K1 K2 : Cat]
  (E : τ (Functor (Op_cat K1) (Catd_cat K2)))
  : Cat
≔ Op_cat
    (@Sigma_cat
      (Op_cat K1)
      (@homdc_op_edge_catd K1 K2 E));

// Constructor-visible object (x1,(x2,u)) of the derived total.
symbol homdc_total_obj
  [K1 K2 : Cat]
  (E : τ (Functor (Op_cat K1) (Catd_cat K2)))
  (x1 : τ (Obj K1))
  (x2 : τ (Obj K2))
  (u : τ (Obj (Fibre_cat
    (@fapp0 (Op_cat K1) (Catd_cat K2) E x1)
    x2)))
  : τ (Obj (@homdc_total_cat K1 K2 E))
≔ Struct_sigma x1 (Struct_sigma x2 u);

// First endpoint projection: opposite of the outer Sigma projection.
symbol homdc_total_source_func
  [K1 K2 : Cat]
  (E : τ (Functor (Op_cat K1) (Catd_cat K2)))
  : τ (Functor (@homdc_total_cat K1 K2 E) K1)
≔ @Op_func
    (@Sigma_cat
      (Op_cat K1)
      (@homdc_op_edge_catd K1 K2 E))
    (Op_cat K1)
    (@Sigma_proj1_func
      (Op_cat K1)
      (@homdc_op_edge_catd K1 K2 E));

// Pointwise inner Sigma projection, reversed in both fibre and base variance.
symbol homdc_total_target_funcd
  [K1 K2 : Cat]
  (E : τ (Functor (Op_cat K1) (Catd_cat K2)))
  : τ (Functord
      (@homdc_op_edge_catd K1 K2 E)
      (@Const_catd (Op_cat K1) (Op_cat K2)))
≔ @Op_funcd
    (Op_cat K1)
    (@homdc_edge_catd K1 K2 E)
    (@Const_catd (Op_cat K1) K2)
    (@sigma_proj1_family_funcd (Op_cat K1) K2 E);

// Totalize that displayed projection and retain only its K2 coordinate.
symbol homdc_total_target_underlying_func
  [K1 K2 : Cat]
  (E : τ (Functor (Op_cat K1) (Catd_cat K2)))
  : τ (Functor
      (@Sigma_cat
        (Op_cat K1)
        (@homdc_op_edge_catd K1 K2 E))
      (Op_cat K2))
≔ @comp_cat_fapp0
    (@Sigma_cat
      (Op_cat K1)
      (@homdc_op_edge_catd K1 K2 E))
    (Product_cat (Op_cat K1) (Op_cat K2))
    (Op_cat K2)
    (@Product_projR_func (Op_cat K1) (Op_cat K2))
    (@sigma_map_func
      (Op_cat K1)
      (@homdc_op_edge_catd K1 K2 E)
      (@Const_catd (Op_cat K1) (Op_cat K2))
      (@homdc_total_target_funcd K1 K2 E));

// Second endpoint projection. Generic fapp1 retains its whole arrow action;
// a later focused row may add a propositional visible-b observation without
// changing this derived owner.
symbol homdc_total_target_func
  [K1 K2 : Cat]
  (E : τ (Functor (Op_cat K1) (Catd_cat K2)))
  : τ (Functor (@homdc_total_cat K1 K2 E) K2)
≔ @Op_func
    (@Sigma_cat
      (Op_cat K1)
      (@homdc_op_edge_catd K1 K2 E))
    (Op_cat K2)
    (@homdc_total_target_underlying_func K1 K2 E);

// Selected ordinary lax-arrow specialization.
symbol LaxArrow_cat
  (C : Cat)
  : Cat
≔ @homdc_total_cat
    C C
    (@hom_int C C (@id_func C));

symbol lax_edge
  [C : Cat]
  (x y : τ (Obj C))
  (u : τ (Hom C x y))
  : τ (Obj (@LaxArrow_cat C))
≔ @homdc_total_obj
    C C
    (@hom_int C C (@id_func C))
    x y u;

// Constructor-visible lax square.  The same nested pair is supplied by the
// generic Hom of homdc_total_cat; alpha is not a postulated square owner.
symbol lax_square
  [C : Cat]
  [x1 y1 x2 y2 : τ (Obj C)]
  (u : τ (Hom C x1 x2))
  (v : τ (Hom C y1 y2))
  (a : τ (Hom C x1 y1))
  (b : τ (Hom C x2 y2))
  (alpha : τ (Obj
    (@homdc_fibre
      C C
      (@hom_int C C (@id_func C))
      x1 y1 x2 y2 u v a b)))
  : τ (Hom
      (@LaxArrow_cat C)
      (@lax_edge C x1 x2 u)
      (@lax_edge C y1 y2 v))
≔ Struct_sigma a (Struct_sigma b alpha);
