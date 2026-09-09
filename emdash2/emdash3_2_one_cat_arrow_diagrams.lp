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
