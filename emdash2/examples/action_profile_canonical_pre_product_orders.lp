/* Product observations of the actual canonical pre-route. */
require open emdash.emdash3_2;

assert [A K C : Cat] (F : τ (Functor A K)) (E : τ (Catd K))
  (FF : τ (@Functord K E (@Const_catd K C))) (a : τ (Obj A))
  (u : τ (Obj (@Fibre_cat K E (@fapp0 A K F a)))) ⊢
 sigma_Fst (@fapp0 (@Sigma_cat A (@Pullback_catd A K E F)) (Product_cat K C) (@hom_precomp_along_fapp0 (@Catd_cat K) Cat_cat
      (@comp_cat_fapp0 (@Catd_cat K) (@Catd_cat A) Cat_cat (@Sigma_func A) (@Pullback_catd_func A K F))
      (Product_cat K C) E (@Const_catd K C) FF (@sigma_pullback_total_func A K F (@Const_catd K C))) (@Struct_sigma (Obj A) (λ b : τ (Obj A), Obj (@Fibre_cat K E (@fapp0 A K F b))) a u))
 ≡ @fapp0 A K F a;

assert [A K C : Cat] (F : τ (Functor A K)) (E : τ (Catd K))
  (FF : τ (@Functord K E (@Const_catd K C))) (a : τ (Obj A))
  (u : τ (Obj (@Fibre_cat K E (@fapp0 A K F a)))) ⊢
 @fapp0 (@Sigma_cat A (@Pullback_catd A K E F)) K (sigma_Fst (@hom_precomp_along_fapp0 (@Catd_cat K) Cat_cat
      (@comp_cat_fapp0 (@Catd_cat K) (@Catd_cat A) Cat_cat (@Sigma_func A) (@Pullback_catd_func A K F))
      (Product_cat K C) E (@Const_catd K C) FF (@sigma_pullback_total_func A K F (@Const_catd K C)))) (@Struct_sigma (Obj A) (λ b : τ (Obj A), Obj (@Fibre_cat K E (@fapp0 A K F b))) a u)
 ≡ @fapp0 A K F a;

assert [A K C : Cat] (F : τ (Functor A K)) (E : τ (Catd K))
  (FF : τ (@Functord K E (@Const_catd K C))) (a : τ (Obj A))
  (u : τ (Obj (@Fibre_cat K E (@fapp0 A K F a)))) ⊢
 sigma_Snd (@fapp0 (@Sigma_cat A (@Pullback_catd A K E F)) (Product_cat K C) (@hom_precomp_along_fapp0 (@Catd_cat K) Cat_cat
      (@comp_cat_fapp0 (@Catd_cat K) (@Catd_cat A) Cat_cat (@Sigma_func A) (@Pullback_catd_func A K F))
      (Product_cat K C) E (@Const_catd K C) FF (@sigma_pullback_total_func A K F (@Const_catd K C))) (@Struct_sigma (Obj A) (λ b : τ (Obj A), Obj (@Fibre_cat K E (@fapp0 A K F b))) a u))
 ≡ @fapp0 (@Fibre_cat K E (@fapp0 A K F a)) C (@Fibre_func K E (@Const_catd K C) FF (@fapp0 A K F a)) u;

assert [A K C : Cat] (F : τ (Functor A K)) (E : τ (Catd K))
  (FF : τ (@Functord K E (@Const_catd K C))) (a : τ (Obj A))
  (u : τ (Obj (@Fibre_cat K E (@fapp0 A K F a)))) ⊢
 @fapp0 (@Sigma_cat A (@Pullback_catd A K E F)) C (sigma_Snd (@hom_precomp_along_fapp0 (@Catd_cat K) Cat_cat
      (@comp_cat_fapp0 (@Catd_cat K) (@Catd_cat A) Cat_cat (@Sigma_func A) (@Pullback_catd_func A K F))
      (Product_cat K C) E (@Const_catd K C) FF (@sigma_pullback_total_func A K F (@Const_catd K C)))) (@Struct_sigma (Obj A) (λ b : τ (Obj A), Obj (@Fibre_cat K E (@fapp0 A K F b))) a u)
 ≡ @fapp0 (@Fibre_cat K E (@fapp0 A K F a)) C (@Fibre_func K E (@Const_catd K C) FF (@fapp0 A K F a)) u;
