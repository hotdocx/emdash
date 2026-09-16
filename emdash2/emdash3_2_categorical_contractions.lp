/*
  Whole categorical contraction along the canonical weakening functor.

  CatContraction and CatdContraction are transparent instances of the existing
  OmegaEquivAlong interface, with its selected inverse functors and whole
  equality-valued inverse laws. They do not assert that IsContr(Obj C)
  contracts directed higher arrows or derive this data from object univalence.
  In the family case the selected inverse is one whole Functord; evaluating
  that same data produces the individual fibre contraction.

  Object/core contractibility is only a derived observation. The along-view
  retains an arbitrary supplied forward map into Terminal_cat, for consumers
  such as adjunction mates; it does not cast that map to Terminal_func.
  No rewrite/unification rules or new structural primitives are introduced.
*/
require open emdash.emdash3_2_eq1_evidence_property;
require open emdash.emdash3_2_nat_arithmetic;

// Whole-category contraction with canonical forward functor.
symbol CatContraction (C : Cat) : Grpd
≔ @OmegaEquivAlong Cat_cat C Terminal_cat (Terminal_func C);

// Selected left inverse; the original evidence also retains its right inverse.
symbol cat_contraction_inverse [C : Cat] (H : τ (CatContraction C))
  : τ (Functor Terminal_cat C)
≔ @omega_equiv_along_left_inv Cat_cat C Terminal_cat (Terminal_func C) H;

// The chosen object is evaluation of the retained whole inverse.
symbol cat_contraction_center [C : Cat] (H : τ (CatContraction C)) : τ (Obj C)
≔ @fapp0 Terminal_cat C (@cat_contraction_inverse C H) Terminal_obj;

// An observation along the actual forward map; do not cast it to Terminal_func.
symbol cat_contraction_objects_along [C : Cat] (F : τ (Functor C Terminal_cat))
  (H : τ (@OmegaEquivAlong Cat_cat C Terminal_cat F))
  : τ (IsContr (Obj C))
≔ @is_contr_retract Unit_grpd (Obj C)
    (λ u : τ Unit_grpd,
      @fapp0 Terminal_cat C
        (@omega_equiv_along_left_inv Cat_cat C Terminal_cat F H) u)
    (λ x : τ (Obj C), @fapp0 C Terminal_cat F x)
    (λ x : τ (Obj C),
      @eq_ap (Functor C C) (Obj C)
        (λ G : τ (Functor C C), @fapp0 C C G x)
        (@comp_cat_fapp0 C Terminal_cat C
          (@omega_equiv_along_left_inv Cat_cat C Terminal_cat F H) F)
        (@id_func C)
        (@omega_equiv_along_left_law Cat_cat C Terminal_cat F H))
    (@is_contr_recenter Unit_grpd unit_is_contr Terminal_obj);

// Canonical-forward specialization of the derived ordinary observation.
symbol cat_contraction_objects [C : Cat] (H : τ (CatContraction C))
  : τ (IsContr (Obj C))
≔ @cat_contraction_objects_along C (Terminal_func C) H;

// One coherent family contraction, not a product of pointwise witnesses.
symbol CatdContraction [K : Cat] (E : τ (Catd K)) : Grpd
≔ @OmegaEquivAlong (Catd_cat K) E (@Const_catd K Terminal_cat)
    (@Terminal_funcd K E);

// The inverse is retained as a whole dependent functor.
symbol catd_contraction_inverse [K : Cat] [E : τ (Catd K)]
  (H : τ (@CatdContraction K E)) : τ (@Functord K (@Const_catd K Terminal_cat) E)
≔ @omega_equiv_along_left_inv (Catd_cat K) E (@Const_catd K Terminal_cat)
    (@Terminal_funcd K E) H;

// Evaluation maps the existing whole inverse data and laws.
symbol catd_contraction_at [K : Cat] [E : τ (Catd K)]
  (H : τ (@CatdContraction K E)) (x : τ (Obj K))
  : τ (CatContraction (@Fibre_cat K E x))
≔ @omega_equiv_along_fapp1_fapp0 (Catd_cat K) Cat_cat
    (@fapp0_func K Cat_cat x) E (@Const_catd K Terminal_cat)
    (@Terminal_funcd K E) H;

// Ordinary fibre contractibility is a downstream observation.
symbol catd_contraction_objects_at [K : Cat] [E : τ (Catd K)]
  (H : τ (@CatdContraction K E)) (x : τ (Obj K))
  : τ (IsContr (Obj (@Fibre_cat K E x)))
≔ @cat_contraction_objects (@Fibre_cat K E x) (@catd_contraction_at K E H x);
