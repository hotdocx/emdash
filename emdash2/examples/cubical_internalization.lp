/*
  Reviewer example: the two-sided cubical internal hom and lax-arrow category
  are derived from ordinary Sigma, pointwise opposite, and homd_int.

  The canonical projection order is target edge, source edge, then the first
  side arrow.  The remaining Sigma-Hom object is (b,alpha), where

    alpha : b o u ==> v o a.

  No primitive cubical category, two-sided Sigma, square, rule, or unifier is
  introduced by the construction.
*/

require open emdash.emdash3_2_cubical_internalization;

// The internal owner is literally the existing homd_int of the pointwise
// opposite inner edge family.
assert [K1 K2 : Cat]
  (E : τ (Functor (Op_cat K1) (Catd_cat K2))) ⊢
  @homdc_int K1 K2 E
  ≡ @homd_int
      (Op_cat K1)
      (@homdc_op_edge_catd K1 K2 E)
      (@homdc_op_edge_catd K1 K2 E)
      (@id_funcd
        (Op_cat K1)
        (@homdc_op_edge_catd K1 K2 E));

// At a fixed first side arrow, the target-first internalization is exactly
// the pointwise opposite of the earlier fixed-endpoint inner total.
assert [K1 K2 : Cat]
  (E : τ (Functor (Op_cat K1) (Catd_cat K2)))
  (x1 y1 : τ (Obj K1))
  (x2 y2 : τ (Obj K2))
  (u : τ (Obj (Fibre_cat
    (@fapp0 (Op_cat K1) (Catd_cat K2) E x1)
    x2)))
  (v : τ (Obj (Fibre_cat
    (@fapp0 (Op_cat K1) (Catd_cat K2) E y1)
    y2)))
  (a : τ (Hom K1 x1 y1)) ⊢
  @homdc_at K1 K2 E y1 y2 v x1 x2 u a
  ≡ Op_cat
      (@fapp0
        (Hom_cat K1 x1 y1)
        Cat_cat
        (@homdc_inner_total_func K1 K2 E x1 y1 x2 y2 u v)
        a);

// The selected ordinary specialization has the expected lax-square object.
assert [C : Cat]
  [x1 y1 x2 y2 : τ (Obj C)]
  (u : τ (Hom C x1 x2))
  (v : τ (Hom C y1 y2))
  (a : τ (Hom C x1 y1))
  (b : τ (Hom C x2 y2))
  (alpha : τ (Hom
    (Hom_cat C x1 y2)
    (@comp_fapp0 C x1 x2 y2 b u)
    (@comp_fapp0 C x1 y1 y2 v a))) ⊢
  @lax_square C x1 y1 x2 y2 u v a b alpha
  : τ (Hom
      (@LaxArrow_cat C)
      (@lax_edge C x1 x2 u)
      (@lax_edge C y1 y2 v));

// Both endpoint projections compute on edge objects.
assert [C : Cat]
  (x y : τ (Obj C))
  (u : τ (Hom C x y)) ⊢
  @fapp0
    (@LaxArrow_cat C)
    C
    (@homdc_total_source_func
      C C (@hom_int C C (@id_func C)))
    (@lax_edge C x y u)
  ≡ x;

assert [C : Cat]
  (x y : τ (Obj C))
  (u : τ (Hom C x y)) ⊢
  @fapp0
    (@LaxArrow_cat C)
    C
    (@homdc_total_target_func
      C C (@hom_int C C (@id_func C)))
    (@lax_edge C x y u)
  ≡ y;

// Source action computes to a. Target action remains a typed whole generic
// action while its optional readable b-observation is still consumer-gated.
assert [C : Cat]
  [x1 y1 x2 y2 : τ (Obj C)]
  (u : τ (Hom C x1 x2))
  (v : τ (Hom C y1 y2))
  (a : τ (Hom C x1 y1))
  (b : τ (Hom C x2 y2))
  (alpha : τ (Hom
    (Hom_cat C x1 y2)
    (@comp_fapp0 C x1 x2 y2 b u)
    (@comp_fapp0 C x1 y1 y2 v a))) ⊢
  @fapp1_fapp0
    (@LaxArrow_cat C)
    C
    (@homdc_total_source_func
      C C (@hom_int C C (@id_func C)))
    (@lax_edge C x1 x2 u)
    (@lax_edge C y1 y2 v)
    (@lax_square C x1 y1 x2 y2 u v a b alpha)
  ≡ a;

assert [C : Cat]
  [x1 y1 x2 y2 : τ (Obj C)]
  (u : τ (Hom C x1 x2))
  (v : τ (Hom C y1 y2))
  (a : τ (Hom C x1 y1))
  (b : τ (Hom C x2 y2))
  (alpha : τ (Hom
    (Hom_cat C x1 y2)
    (@comp_fapp0 C x1 x2 y2 b u)
    (@comp_fapp0 C x1 y1 y2 v a))) ⊢
  @fapp1_fapp0
    (@LaxArrow_cat C)
    C
    (@homdc_total_target_func
      C C (@hom_int C C (@id_func C)))
    (@lax_edge C x1 x2 u)
    (@lax_edge C y1 y2 v)
    (@lax_square C x1 y1 x2 y2 u v a b alpha)
  : τ (Hom C x2 y2);

// The whole endpoint hom actions remain available for another dimension.
type @homdc_int;
type @homdc_total_source_func;
type @homdc_total_target_func;
