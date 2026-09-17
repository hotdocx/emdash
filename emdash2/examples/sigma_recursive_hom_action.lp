/* Recursive Hom action of the existing Sigma projection, base change and section total. */
require open emdash.emdash3_2;
// catalog-area: Sigma totals and recursive Hom action

symbol sigma_review_lift [K L : Cat] (F : τ (Functor K L)) (E : τ (Catd L))
 (s : τ (Obj (@Pi_cat K (@Pullback_catd K L E F))))
 : τ (Functor K (@Sigma_cat L E))
≔ @comp_cat_fapp0 K (@Sigma_cat K (@Pullback_catd K L E F)) (@Sigma_cat L E)
 (@sigma_pullback_total_func K L F E) (@section_total_func K (@Pullback_catd K L E F) s);

symbol sigma_review_base [K L : Cat] (F : τ (Functor K L)) (E : τ (Catd L))
 (s : τ (Obj (@Pi_cat K (@Pullback_catd K L E F)))) : τ (Functor K L)
≔ @comp_cat_fapp0 K (@Sigma_cat L E) L (@Sigma_proj1_func L E) (@sigma_review_lift K L F E s);

// The whole lifted section retains the original base functor.
assert [K L : Cat] (F : τ (Functor K L)) (E : τ (Catd L)) (s : τ (Obj (@Pi_cat K (@Pullback_catd K L E F)))) (x : τ (Obj K)) ⊢ @fapp0 K L (@sigma_review_base K L F E s) x ≡ @fapp0 K L F x;
assert [K L : Cat] (F : τ (Functor K L)) (E : τ (Catd L)) (s : τ (Obj (@Pi_cat K (@Pullback_catd K L E F)))) (x y : τ (Obj K)) (p : τ (Hom K x y)) ⊢ @fapp1_fapp0 K L (@sigma_review_base K L F E s) x y p ≡ @fapp1_fapp0 K L F x y p;

// Arbitrary second and third cells exercise recursive whole action.
assert [K L : Cat] (F : τ (Functor K L)) (E : τ (Catd L)) (s : τ (Obj (@Pi_cat K (@Pullback_catd K L E F)))) (x y : τ (Obj K)) (p q : τ (Hom K x y)) (theta : τ (Hom (Hom_cat K x y) p q)) ⊢ @fapp1_fapp0 (Hom_cat K x y) (Hom_cat L (@fapp0 K L F x) (@fapp0 K L F y)) (@fapp1_func K L (@sigma_review_base K L F E s) x y) p q theta ≡ @fapp1_fapp0 (Hom_cat K x y) (Hom_cat L (@fapp0 K L F x) (@fapp0 K L F y)) (@fapp1_func K L F x y) p q theta;
assert [K L : Cat] (F : τ (Functor K L)) (E : τ (Catd L)) (s : τ (Obj (@Pi_cat K (@Pullback_catd K L E F)))) (x y : τ (Obj K)) (p q : τ (Hom K x y)) (theta eta : τ (Hom (Hom_cat K x y) p q)) (xi : τ (Hom (Hom_cat (Hom_cat K x y) p q) theta eta)) ⊢ @fapp1_fapp0 (Hom_cat (Hom_cat K x y) p q) (Hom_cat (Hom_cat L (@fapp0 K L F x) (@fapp0 K L F y)) (@fapp1_fapp0 K L F x y p) (@fapp1_fapp0 K L F x y q)) (@fapp1_func (Hom_cat K x y) (Hom_cat L (@fapp0 K L F x) (@fapp0 K L F y)) (@fapp1_func K L (@sigma_review_base K L F E s) x y) p q) theta eta xi ≡ @fapp1_fapp0 (Hom_cat (Hom_cat K x y) p q) (Hom_cat (Hom_cat L (@fapp0 K L F x) (@fapp0 K L F y)) (@fapp1_fapp0 K L F x y p) (@fapp1_fapp0 K L F x y q)) (@fapp1_func (Hom_cat K x y) (Hom_cat L (@fapp0 K L F x) (@fapp0 K L F y)) (@fapp1_func K L F x y) p q) theta eta xi;

// Preserve the original first-Hom identity computation in both owners.
assert [K : Cat] (E : τ (Catd K)) (x : τ (Obj K)) (u : τ (Obj (@Fibre_cat K E x))) ⊢
 @fapp0 _ _ (@fapp1_func (@Sigma_cat K E) K (@Sigma_proj1_func K E) (Struct_sigma x u) (Struct_sigma x u))
   (@id (@Sigma_cat K E) (Struct_sigma x u)) ≡ @id K x;
assert [K L : Cat] (F : τ (Functor K L)) (E : τ (Catd L)) (x : τ (Obj K))
 (u : τ (Obj (@Fibre_cat L E (@fapp0 K L F x)))) ⊢
 @fapp0 _ _ (@fapp1_func _ _ (@sigma_pullback_total_func K L F E) (Struct_sigma x u) (Struct_sigma x u))
   (@id (@Sigma_cat K (@Pullback_catd K L E F)) (Struct_sigma x u))
 ≡ @id (@Sigma_cat L E) (Struct_sigma (@fapp0 K L F x) u);

// Section-total Hom evaluation agrees with its existing capped action.
assert [K : Cat] (E : τ (Catd K)) (s : τ (Obj (@Pi_cat K E)))
 (x y : τ (Obj K)) (p : τ (Hom K x y)) ⊢
 @fapp0 _ _ (@fapp1_func K (@Sigma_cat K E) (@section_total_func K E s) x y) p
 ≡ @fapp1_fapp0 K (@Sigma_cat K E) (@section_total_func K E s) x y p;

// Normal-form guard: retain the first Hom head and its original cuts.
assertnot [K : Cat] (E : τ (Catd K)) (x y : τ (Obj K))
 (u : τ (Obj (@Fibre_cat K E x))) (v : τ (Obj (@Fibre_cat K E y))) ⊢
 @fapp1_func (@Sigma_cat K E) K (@Sigma_proj1_func K E) (Struct_sigma x u) (Struct_sigma y v)
 ≡ @Op_func
   (@Sigma_cat (Op_cat (Hom_cat K x y)) (@homd_ K E E (@id_funcd K E) x u y v))
   (Op_cat (Hom_cat K x y))
   (@Sigma_proj1_func (Op_cat (Hom_cat K x y)) (@homd_ K E E (@id_funcd K E) x u y v));
