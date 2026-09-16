/* Derived ordinary equality of existing native square objects.
   OneCat makes each filler Hom proposition-valued. The proof uses constructor
   congruence at the actual native Hom, without identifying its classifier
   with an externally written tuple type or adding any primitive/rule. */
require open emdash.emdash3_2_cubical_arrow;
require open emdash.emdash3_2_eq1_evidence_property;
require open emdash.emdash3_2_prop_fibre_constructor_paths;

symbol one_cat_square_filler_is_prop [C : Cat]
  (C1 : τ (IsNCat (cat_succ cat_zero) C))
  [x0 x1 y0 y1 : τ (Obj C)]
  (u : τ (Hom C x0 y0)) (v : τ (Hom C x1 y1))
  (a : τ (Hom C x0 x1)) (b : τ (Hom C y0 y1))
  : τ (IsPropGrpd (Obj (@homdc_square_fibre C x0 x1 y0 y1 u v a b)))
≔ @discrete_hom_is_prop (Hom_cat C x0 y1) (C1 x0 y1)
    (@comp_fapp0 C x0 y0 y1 b u) (@comp_fapp0 C x0 x1 y1 v a);

symbol one_cat_native_square_path [C : Cat]
  (C1 : τ (IsNCat (cat_succ cat_zero) C))
  [x0 x1 y0 y1 : τ (Obj C)]
  (u : τ (Hom C x0 y0)) (v : τ (Hom C x1 y1))
  [a a1 : τ (Hom C x0 x1)] [b b1 : τ (Hom C y0 y1)]
  (alpha : τ (Obj (@homdc_square_fibre C x0 x1 y0 y1 u v a b)))
  (beta : τ (Obj (@homdc_square_fibre C x0 x1 y0 y1 u v a1 b1)))
  (p : τ (@= (Hom C x0 x1) a a1)) (q : τ (@= (Hom C y0 y1) b b1))
  : τ (@= (Hom (@LaxArrow_cat C) (@lax_edge C x0 y0 u) (@lax_edge C x1 y1 v))
    (@lax_square C x0 x1 y0 y1 u v a b alpha)
    (@lax_square C x0 x1 y0 y1 u v a1 b1 beta))
≔ @two_prop_fibre_image_path (Hom C x0 x1) (Hom C y0 y1)
    (Hom (@LaxArrow_cat C) (@lax_edge C x0 y0 u) (@lax_edge C x1 y1 v))
    (λ a0 : τ (Hom C x0 x1), λ b0 : τ (Hom C y0 y1),
      Obj (@homdc_square_fibre C x0 x1 y0 y1 u v a0 b0))
    (λ a0 : τ (Hom C x0 x1), λ b0 : τ (Hom C y0 y1),
      λ gamma : τ (Obj (@homdc_square_fibre C x0 x1 y0 y1 u v a0 b0)),
      @lax_square C x0 x1 y0 y1 u v a0 b0 gamma)
    (@one_cat_square_filler_is_prop C C1 x0 x1 y0 y1 u v)
    a b alpha a1 b1 beta p q;
