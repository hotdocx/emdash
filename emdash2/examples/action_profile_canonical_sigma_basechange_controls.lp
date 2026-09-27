/* Canonical pre/post base-change components and ambient noncollapse. */
require open emdash.emdash3_2;

assert [A K : Cat] (F : τ (Functor A K)) (E D : τ (Catd K))
  (FF : τ (@Functord K E D)) (a : τ (Obj A))
  (u : τ (Obj (@Fibre_cat K E (@fapp0 A K F a)))) ⊢
  @tapp0_fapp0 (@Sigma_cat A (@Pullback_catd A K E F)) (@Sigma_cat K D) _ _
    (Struct_sigma a u)
    (@tapp1_pre_laxity_cell (@Catd_cat K) Cat_cat
      (@comp_cat_fapp0 (@Catd_cat K) (@Catd_cat A) Cat_cat (@Sigma_func A) (@Pullback_catd_func A K F))
      (@Sigma_func K) (@sigma_pullback_total_transf A K F) E D D FF (@id (@Catd_cat K) D))
  ≡ @id (@Sigma_cat K D)
      (Struct_sigma (@fapp0 A K F a)
        (@fapp0 (@Fibre_cat K E (@fapp0 A K F a)) (@Fibre_cat K D (@fapp0 A K F a))
          (@Fibre_func K E D FF (@fapp0 A K F a)) u));

assert [A K : Cat] (F : τ (Functor A K)) (E D : τ (Catd K))
  (FF : τ (@Functord K E D)) (a : τ (Obj A))
  (u : τ (Obj (@Fibre_cat K E (@fapp0 A K F a)))) ⊢
  @tapp0_fapp0 (@Sigma_cat A (@Pullback_catd A K E F)) (@Sigma_cat K D) _ _
    (Struct_sigma a u)
    (@tapp1_post_laxity_cell (@Catd_cat K) Cat_cat
      (@comp_cat_fapp0 (@Catd_cat K) (@Catd_cat A) Cat_cat (@Sigma_func A) (@Pullback_catd_func A K F))
      (@Sigma_func K) (@sigma_pullback_total_transf A K F) E E D FF (@id (@Catd_cat K) E))
  ≡ @id (@Sigma_cat K D)
      (Struct_sigma (@fapp0 A K F a)
        (@fapp0 (@Fibre_cat K E (@fapp0 A K F a)) (@Fibre_cat K D (@fapp0 A K F a))
          (@Fibre_func K E D FF (@fapp0 A K F a)) u));

assertnot [A : Cat] (F : τ (Functor A Cat_cat)) (Z : Cat)
  (W X : τ (Obj A)) (h : τ (Hom A W X)) (G : τ (Functor (@fapp0 A Cat_cat F X) Z)) ⊢
  @hom_precomp_along_fapp0 A Cat_cat F Z W X h G
  ≡ @comp_cat_fapp0 (@fapp0 A Cat_cat F W) (@fapp0 A Cat_cat F X) Z G (@fapp1_fapp0 A Cat_cat F W X h);

assertnot [A B : Cat] (F : τ (Functor A B)) [x y z : τ (Obj A)]
  (f : τ (Hom A x y)) (g : τ (Hom A y z)) ⊢
  @eq_refl (Hom B (@fapp0 A B F x) (@fapp0 A B F z))
    (@fapp1_fapp0 A B F x z (@comp_fapp0 A x y z g f))
  : τ (@= (Hom B (@fapp0 A B F x) (@fapp0 A B F z))
      (@fapp1_fapp0 A B F x z (@comp_fapp0 A x y z g f))
      (@comp_fapp0 B _ _ _ (@fapp1_fapp0 A B F y z g) (@fapp1_fapp0 A B F x y f)));

// Canonical pre-route object observation retains its whole functor owner.
assert [A K : Cat] (F : τ (Functor A K)) (E D : τ (Catd K))
  (FF : τ (@Functord K E D)) (a : τ (Obj A))
  (u : τ (Obj (@Fibre_cat K E (@fapp0 A K F a)))) ⊢
  @fapp0 _ _
    (@hom_precomp_along_fapp0 (@Catd_cat K) Cat_cat
      (@comp_cat_fapp0 (@Catd_cat K) (@Catd_cat A) Cat_cat (@Sigma_func A) (@Pullback_catd_func A K F))
      (@Sigma_cat K D) E D FF (@sigma_pullback_total_func A K F D))
    (Struct_sigma a u)
  ≡ @Struct_sigma (Obj K) (λ k : τ (Obj K), Obj (@Fibre_cat K D k)) (@fapp0 A K F a)
      (@fapp0 (@Fibre_cat K E (@fapp0 A K F a)) (@Fibre_cat K D (@fapp0 A K F a))
        (@Fibre_func K E D FF (@fapp0 A K F a)) u);
