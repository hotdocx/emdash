require open emdash.emdash3_2_cubical_arrow;
require open emdash.emdash3_2_arrow_diagram_families;

/* Ordinary-target realization of the existing native arrow category. */

// Native squares in a OneCat target express the naturality of this family.
// There is no extra caller-supplied square or a new arrow-category carrier.
injective symbol one_cat_arrow_universal_transf
  [C : Cat] (C1 : τ (IsNCat (cat_succ cat_zero) C))
  : τ (@Transf (@LaxArrow_cat C) C (@cubical_src_func C) (@cubical_tgt_func C));

rule @tapp0_fapp0 _ _ _ _
      (Struct_sigma _ (Struct_sigma _ $u))
      (@one_cat_arrow_universal_transf _ _)
  ↪ $u;

symbol one_cat_arrow_diagram_func
  [C : Cat] (C1 : τ (IsNCat (cat_succ cat_zero) C))
  : τ (Functor (@LaxArrow_cat C) (Functor_cat WalkingArrow_cat C))
≔ @transf_arrow_diagram_func (@LaxArrow_cat C) C
    (@cubical_src_func C) (@cubical_tgt_func C)
    (@one_cat_arrow_universal_transf C C1);

// The existing whole square action, viewed at its introduced endpoints.
// Endpoint comparison uses the established diagram-point unifier.
symbol one_cat_square_diagram_transf
  [C : Cat] (C1 : τ (IsNCat (cat_succ cat_zero) C))
  [X0 X1 Y0 Y1 : τ (Obj C)]
  (u : τ (Hom C X0 Y0)) (v : τ (Hom C X1 Y1))
  (a : τ (Hom C X0 X1)) (b : τ (Hom C Y0 Y1))
  (alpha : τ (Obj (@homdc_square_fibre C X0 X1 Y0 Y1 u v a b)))
  : τ (@Transf WalkingArrow_cat C
      (@walking_arrow_func C X0 Y0 u) (@walking_arrow_func C X1 Y1 v))
≔ @fapp1_fapp0 (@LaxArrow_cat C) (Functor_cat WalkingArrow_cat C)
    (@one_cat_arrow_diagram_func C C1)
    (@lax_edge C X0 Y0 u) (@lax_edge C X1 Y1 v)
    (@lax_square C X0 X1 Y0 Y1 u v a b alpha);
