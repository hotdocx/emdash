require open emdash.emdash3_2;

// catalog-area: Sigma/Pi whole projection views

// Reindexing compares the original family, not an arbitrary alternative.
assert [A B C : Cat] (E : τ (Catd C))
 (F : τ (Functor B C)) (G : τ (Functor A B)) ⊢
 @eq_refl (Catd A) (@Op_catd A
   (@comp_cat_fapp0 A B Cat_cat (@comp_cat_fapp0 B C Cat_cat E F) G))
 : τ (@= (Catd A)
     (@Op_catd A (@comp_cat_fapp0 A B Cat_cat (@comp_cat_fapp0 B C Cat_cat E F) G))
     (@Pullback_catd A C (@Op_catd C E) (@comp_cat_fapp0 A B C F G)));
assertnot [A B C : Cat] (E D : τ (Catd C))
 (F : τ (Functor B C)) (G : τ (Functor A B)) ⊢
 @eq_refl (Catd A) (@Op_catd A
   (@comp_cat_fapp0 A B Cat_cat (@comp_cat_fapp0 B C Cat_cat E F) G))
 : τ (@= (Catd A)
     (@Op_catd A (@comp_cat_fapp0 A B Cat_cat (@comp_cat_fapp0 B C Cat_cat E F) G))
     (@Pullback_catd A C (@Op_catd C D) (@comp_cat_fapp0 A B C F G)));

// Sufficient section congruence does not identify arbitrary maps.
assertnot [K : Cat] (E D : τ (Catd K))
 (FF GG : τ (@Functord K E D)) (s : τ (Obj (@Pi_cat K E))) ⊢
 @eq_refl (Obj (@Pi_cat K D)) (@section_postcomp_sec K E D FF s)
 : τ (@= (Obj (@Pi_cat K D)) (@section_postcomp_sec K E D FF s)
     (@section_postcomp_sec K E D GG s));


// Canonical total base change and the existing identity evaluation order.
assert [A K : Cat] (F : τ (Functor A K)) (E D : τ (Catd K))
 (FF : τ (@Functord K E D)) (a : τ (Obj A))
 (u : τ (Obj (@Fibre_cat K E (@fapp0 A K F a)))) ⊢
 @fapp0 _ _ (@tapp1_fapp0 (@Catd_cat K) Cat_cat
   (@comp_cat_fapp0 (@Catd_cat K) (@Catd_cat A) Cat_cat (@Sigma_func A) (@Pullback_catd_func A K F))
   (@Sigma_func K) E D (@sigma_pullback_total_transf A K F) FF) (Struct_sigma a u)
 ≡ @Struct_sigma (Obj K) (λ k : τ (Obj K), Obj (@Fibre_cat K D k))
     (@fapp0 A K F a) (@fapp0 _ _ (@Fibre_func K E D FF (@fapp0 A K F a)) u);

assert [A K : Cat] (F : τ (Functor A K)) (E : τ (Catd K))
 (a : τ (Obj A)) (u : τ (Obj (@Fibre_cat K E (@fapp0 A K F a)))) ⊢
 @fapp0 _ _ (@tapp1_fapp0 (@Catd_cat K) Cat_cat
   (@comp_cat_fapp0 (@Catd_cat K) (@Catd_cat A) Cat_cat (@Sigma_func A) (@Pullback_catd_func A K F))
   (@Sigma_func K) E E (@sigma_pullback_total_transf A K F) (@id_funcd K E)) (Struct_sigma a u)
 ≡ @Struct_sigma (Obj K) (λ k : τ (Obj K), Obj (@Fibre_cat K E k)) (@fapp0 A K F a) u;

// The contextual congruence requires the outer functors to compare too.
assertnot [A B C : Cat] (F G : τ (Functor B C)) (H : τ (Functor A B)) ⊢
 @eq_refl (Functor A C) (@comp_cat_fapp0 A B C F H)
 : τ (@= (Functor A C) (@comp_cat_fapp0 A B C F H) (@comp_cat_fapp0 A B C G H));

// Constant-total projection view and preserved runtime boundary.
assert [A K C : Cat] (F : τ (Functor A K)) ⊢
 @eq_refl (Functor (Product_cat A C) C)
   (@comp_cat_fapp0 (Product_cat A C) (Product_cat K C) C (@Product_projR_func K C)
     (@sigma_pullback_total_func A K F (@Const_catd K C)))
 : τ (@= (Functor (Product_cat A C) C)
   (@comp_cat_fapp0 (Product_cat A C) (Product_cat K C) C (@Product_projR_func K C)
     (@sigma_pullback_total_func A K F (@Const_catd K C))) (@Product_projR_func A C));
assertnot [A K C : Cat] (F : τ (Functor A K)) ⊢
 @comp_cat_fapp0 (Product_cat A C) (Product_cat K C) C (@Product_projR_func K C)
   (@sigma_pullback_total_func A K F (@Const_catd K C))
 ≡ @Product_projR_func A C;
