/*
  Reviewer: identity observations across the two existing family-pullback
  presentations. Pullback_catd and raw composition remain distinct runtime
  owners. Their existing proof-time comparison types the displayed identity;
  inferred source/target family labels must not block its component or cell
  computation. The actual identity head is required throughout.
*/
require open emdash.emdash3_2;

assert [K B : Cat] (E : τ (Catd B)) (F : τ (Functor K B)) (x : τ (Obj K)) ⊢
  @tapp0_fapp0 K Cat_cat (@Pullback_catd K B E F)
    (@comp_cat_fapp0 K B Cat_cat E F) x
    (@id (Catd_cat K) (@Pullback_catd K B E F))
  ≡ @id Cat_cat (@fapp0 B Cat_cat E (@fapp0 K B F x));

assert [K B : Cat] (E : τ (Catd B)) (F : τ (Functor K B)) (x : τ (Obj K))
  (u : τ (Obj (@fapp0 B Cat_cat E (@fapp0 K B F x)))) ⊢
  @fapp0 _ _ (@tapp0_fapp0 K Cat_cat (@Pullback_catd K B E F)
    (@comp_cat_fapp0 K B Cat_cat E F) x
    (@id (Catd_cat K) (@Pullback_catd K B E F))) u
  ≡ u;

assert [K B : Cat] (E : τ (Catd B)) (F : τ (Functor K B))
  (x y : τ (Obj K)) (p : τ (Hom K x y))
  (u : τ (Obj (@Fibre_cat K (@Pullback_catd K B E F) x)))
  (v : τ (Obj (@Fibre_cat K (@Pullback_catd K B E F) y)))
  (alpha : τ (Obj (@fapp0 (Op_cat (Hom_cat K x y)) Cat_cat
    (@homd_ K (@Pullback_catd K B E F) (@Pullback_catd K B E F)
      (@id_funcd K (@Pullback_catd K B E F)) x u y v) p))) ⊢
  @fdapp1_int_hom_fapp0 K (@Pullback_catd K B E F)
    (@comp_cat_fapp0 K B Cat_cat E F)
    (@id (Catd_cat K) (@Pullback_catd K B E F)) x y p u v alpha
  ≡ alpha;

// An arbitrary whole displayed functor is not collapsed to the identity.
assertnot [K : Cat] (E : τ (Catd K)) (H : τ (@Functord K E E)) (x : τ (Obj K)) ⊢
  @tapp0_fapp0 K Cat_cat E E x H ≡ @id Cat_cat (@Fibre_cat K E x);
