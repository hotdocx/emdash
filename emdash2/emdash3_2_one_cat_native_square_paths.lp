/* Derived ordinary equality of existing native square objects.
   OneCat makes each filler Hom proposition-valued. The proof uses constructor
   congruence at the actual native Hom, without identifying its classifier
   with an externally written tuple type or adding any primitive/rule. */
require open emdash.emdash3_2_cubical_arrow;
require open emdash.emdash3_2_eq1_evidence_property;

// Dependent constructor congruence when the last fibre is a proposition.
// The result stays in the constructor's actual codomain Z.
protected symbol two_prop_fibre_image_path [A B Z : Grpd] (P : τ A → τ B → Grpd)
  (c : Π a0 : τ A, Π b0 : τ B, τ (P a0 b0) → τ Z)
  (hP : Π a0 : τ A, Π b0 : τ B, τ (IsPropGrpd (P a0 b0)))
  [a : τ A] [b : τ B] (u : τ (P a b))
  [a1 : τ A] [b1 : τ B] (v : τ (P a1 b1))
  (p : τ (@= A a a1)) (q : τ (@= B b b1))
  : τ (@= Z (c a b u) (c a1 b1 v))
≔ (@ind_eq A a1 a (@eq_sym A a a1 p)
    (λ a0 : τ A, @Pi_grpd B (λ b0 : τ B,
      @Pi_grpd (P a0 b0) (λ v0 : τ (P a0 b0),
        @Pi_grpd (@= B b b0) (λ q0 : τ (@= B b b0),
          @= Z (c a b u) (c a0 b0 v0)))))
    (λ b0 : τ B, λ v0 : τ (P a b0), λ q0 : τ (@= B b b0),
      (@ind_eq B b0 b (@eq_sym B b b0 q0)
        (λ b2 : τ B, @Pi_grpd (P a b2) (λ v2 : τ (P a b2),
          @= Z (c a b u) (c a b2 v2)))
        (λ v2 : τ (P a b),
          @eq_ap (P a b) Z (c a b) u v2
            (@is_contr_center (@= (P a b) u v2) (hP a b u v2)))) v0)) b1 v q;

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
