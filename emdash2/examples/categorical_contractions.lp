/* Reviewer: whole categorical contractions data and qualified computation. */
require open emdash.emdash3_2_categorical_contractions;
// catalog-area: Categorical contraction and ordinary terminal adjunctions

assert [C : Cat] (H : τ (CatContraction C)) ⊢
  @is_contr_center (Obj C) (@cat_contraction_objects C H)
  ≡ @cat_contraction_center C H;

assert [K : Cat] [E : τ (Catd K)] (H : τ (@CatdContraction K E)) (x : τ (Obj K)) ⊢
  @cat_contraction_inverse (@Fibre_cat K E x) (@catd_contraction_at K E H x)
  ≡ @tapp0_fapp0 K Cat_cat (@Const_catd K Terminal_cat) E x (@catd_contraction_inverse K E H);

// Evaluation retains the independently supplied right inverse as well.
assert [K : Cat] [E : τ (Catd K)] (H : τ (@CatdContraction K E)) (x : τ (Obj K)) ⊢
  @omega_equiv_along_right_inv Cat_cat (@Fibre_cat K E x) Terminal_cat
    (Terminal_func (@Fibre_cat K E x)) (@catd_contraction_at K E H x)
  ≡ @tapp0_fapp0 K Cat_cat (@Const_catd K Terminal_cat) E x
      (@omega_equiv_along_right_inv (Catd_cat K) E (@Const_catd K Terminal_cat)
        (@Terminal_funcd K E) H);

// Whole inverse family action is retained for varying base endpoints.
assert [K : Cat] [E : τ (Catd K)] (H : τ (@CatdContraction K E))
  (x y : τ (Obj K)) ⊢
  @tapp1_func K Cat_cat (@Const_catd K Terminal_cat) E x y
    (@catd_contraction_inverse K E H)
  : τ (Functor (Hom_cat K x y) (Functor_cat Terminal_cat (@Fibre_cat K E y)));

// The inverse's categorical Hom action is available, beyond a chosen object.
assert [C : Cat] (H : τ (CatContraction C)) (u v : τ (Obj Terminal_cat)) ⊢
  @fapp1_func Terminal_cat C (@cat_contraction_inverse C H) u v
  : τ (Functor (Hom_cat Terminal_cat u v)
      (Hom_cat C (@fapp0 Terminal_cat C (@cat_contraction_inverse C H) u)
        (@fapp0 Terminal_cat C (@cat_contraction_inverse C H) v)));
